from itertools import combinations, product

from bedc_quality_lab import discovery
from bedc_quality_lab.classifier_shift import (
    ClassifierPassage,
    ClassifierState,
    classifier_shift,
    classifier_surface_delta,
    shift_information,
    structural_discovery,
)
from bedc_quality_lab.hardening import (
    HardeningBackend,
    HardeningProfile,
    critical_hardening_gap,
    fully_hardened_classifier,
    ledger_only_classifier,
    partially_hardened_classifier,
)
from bedc_quality_lab.ledger import LedgerRowKey, ledger_complete, ledger_gap
from bedc_quality_lab.metrics import classifier_certificate
from bedc_quality_lab.scope import (
    GlobalResolutionClaim,
    Scope,
    ScopedCertificate,
    global_ledger_complete,
    global_required_rows,
    globally_resolved,
    scope_rows,
    scoped_resolved,
    semantic_rows,
    verification_rows,
)


SOURCE_IDS = frozenset({"x", "y"})
BASE_RELATION = frozenset({("x", "x", "same"), ("x", "y", "near"), ("y", "y", "same")})
SHIFTED_RELATION = frozenset({("x", "x", "same"), ("x", "y", "far"), ("y", "y", "same")})
SURFACE_PAIR = ("x", "y")
CLASSIFIER_ROW = LedgerRowKey("classifier", "x->y")
SOURCE_ROW = LedgerRowKey("source", "M:D0")
STABILITY_ROW = LedgerRowKey("stability", "M:A")
LEDGER_ROW = LedgerRowKey("ledger", "boundary")
VERIFY_ROW = LedgerRowKey("verification", "M:B:checked-statement")
TRANSCRIPTION_ROW = LedgerRowKey("verification", "M:B:translation-assumptions")
PROFILE_ROW = LedgerRowKey("ndna", "profile")
POLICY = frozenset({CLASSIFIER_ROW})
CERTIFIED = classifier_certificate(
    {"linear_identifiability_r2": 0.95, "approx_identifiability_proxy": 0.90}
)
UNCERTIFIED = classifier_certificate(
    {"linear_identifiability_r2": 0.10, "approx_identifiability_proxy": 0.10}
)
KERNEL_CHECKED = {**CERTIFIED, "verification_status": "kernel-checked"}
SEMANTIC_CERTIFIED = {**CERTIFIED, "semantic_globalizer": True}


def powerset(rows):
    rows = tuple(rows)
    for size in range(len(rows) + 1):
        for members in combinations(rows, size):
            yield frozenset(members)


def classifier_state(
    *,
    relation=BASE_RELATION,
    certificate=CERTIFIED,
    surface_used=frozenset({SURFACE_PAIR}),
    ledger_policy=POLICY,
    verification_status="unchecked",
):
    return ClassifierState(
        source_ids=SOURCE_IDS,
        pattern_id="formal-verification",
        ledger_policy=ledger_policy,
        relation=relation,
        certificate=certificate,
        surface_used=surface_used,
        verification_status=verification_status,
    )


def passage(
    *,
    shifted=True,
    certificate=CERTIFIED,
    recorded_rows=POLICY,
    surface_used=frozenset({SURFACE_PAIR}),
):
    return ClassifierPassage(
        source=classifier_state(relation=BASE_RELATION),
        target=classifier_state(
            relation=SHIFTED_RELATION if shifted else BASE_RELATION,
            certificate=certificate,
            surface_used=surface_used,
        ),
        recorded_rows=recorded_rows,
    )


def scope(*, behavior_id="B", domain_ids=frozenset({"D0"}), model_id="M"):
    return Scope(
        domain_ids=domain_ids,
        model_id=model_id,
        admitted_family_id="A",
        behavior_id=behavior_id,
    )


def scoped_cert(
    *,
    certificate=CERTIFIED,
    recorded_rows=None,
    required_rows=None,
    boundary=frozenset({"outside-scope"}),
    behavior_id="B",
    domain_ids=frozenset({"D0"}),
):
    cert_scope = scope(behavior_id=behavior_id, domain_ids=domain_ids)
    required = scope_rows(cert_scope) if required_rows is None else required_rows
    return ScopedCertificate(
        scope=cert_scope,
        classifier_id="C",
        namecert_id="N",
        required_rows=required,
        recorded_rows=required if recorded_rows is None else recorded_rows,
        certificate=certificate,
        not_claimed_boundary=boundary,
    )


def global_claim(certificates, *, behavior_family=None, recorded_rows=None):
    family = (
        frozenset(cert.scope.behavior_id for cert in certificates)
        if behavior_family is None
        else behavior_family
    )
    base = GlobalResolutionClaim(
        model_id="M",
        behavior_family=family,
        certificates=tuple(certificates),
        global_recorded_rows=frozenset(),
    )
    return GlobalResolutionClaim(
        model_id="M",
        behavior_family=family,
        certificates=tuple(certificates),
        global_recorded_rows=global_required_rows(base) if recorded_rows is None else recorded_rows,
    )


def backend(rows=frozenset({SOURCE_ROW, CLASSIFIER_ROW, STABILITY_ROW, VERIFY_ROW, PROFILE_ROW})):
    return HardeningBackend("lean", rows)


def hardening_profile(
    *,
    certificate=CERTIFIED,
    required=frozenset({SOURCE_ROW, CLASSIFIER_ROW, STABILITY_ROW, LEDGER_ROW}),
    recorded=frozenset({SOURCE_ROW, CLASSIFIER_ROW, STABILITY_ROW, LEDGER_ROW}),
    critical=frozenset({SOURCE_ROW, CLASSIFIER_ROW}),
    hardened=frozenset(),
    frontier=frozenset(),
    residue=frozenset(),
    empirical=False,
):
    return HardeningProfile(
        certificate=certificate,
        mode_rows=required,
        declared_mode_rows=required,
        open_mode_rows=frozenset(),
        ledger_required_rows=required,
        ledger_recorded_rows=recorded,
        critical_rows=critical,
        hardened_rows=hardened,
        frontier_rows=frontier,
        non_hardenable_residue=residue,
        empirical_stability=empirical,
    )


def discovery_claim(
    *,
    shifted=True,
    certificate=CERTIFIED,
    passage_rows=POLICY,
    claim_rows=POLICY,
    required_rows=POLICY,
    benefit=None,
    score=None,
    debt=None,
    boundary=frozenset({"outside-scope"}),
    scope_sealed=True,
    scoped_certificate=None,
    global_resolution=None,
    omitted=None,
    hardening=None,
    hardening_backend=None,
    ndna_complete=False,
    ndna_anchored=False,
    ndna_namecert_compatible=False,
    ndna_ledger_complete=False,
    ndna_net=0.0,
    reproducible=False,
    verification_assisted=False,
    verification_benefit=0.0,
    verification_required=frozenset(),
    verification_recorded=frozenset(),
    laundering=frozenset(),
):
    cert = scoped_certificate
    if cert is None and global_resolution is None:
        cert = scoped_cert(certificate=certificate, boundary=boundary)
    return discovery.DiscoveryClaim(
        passage=passage(shifted=shifted, certificate=certificate, recorded_rows=passage_rows),
        benefit_terms={"coverage": 1.0} if benefit is None else benefit,
        score_terms={"classifier": 0.1} if score is None else score,
        debt_terms={"ledger": 0.1} if debt is None else debt,
        ledger_required_rows=required_rows,
        ledger_recorded_rows=claim_rows,
        public_cost_protocol=True,
        scope_sealed=scope_sealed,
        not_claimed_boundary=boundary,
        benefit_modes=frozenset({"coverage"}),
        omitted_debt_terms={} if omitted is None else omitted,
        scoped_certificate=cert,
        global_claim=global_resolution,
        hardening_profile=hardening,
        hardening_backend=hardening_backend,
        reproducible_evidence=reproducible,
        ndna_complete=ndna_complete,
        ndna_anchored=ndna_anchored,
        ndna_namecert_compatible=ndna_namecert_compatible,
        ndna_ledger_complete=ndna_ledger_complete,
        ndna_net_information=ndna_net,
        verification_assisted=verification_assisted,
        verification_benefit=verification_benefit,
        verification_required_rows=verification_required,
        verification_recorded_rows=verification_recorded,
        laundering_modes=laundering,
    )


def test_finite_classifier_tables_verifiable_exhaustive():
    """thm:philosophy-finite-classifier-tables-verifiable; Lean: BEDC.GroundCompiler.TheoremGenerated.CertificateSoundTheoremRecognition; primitive: classifier_shift.classifier_surface_delta."""
    relations = (BASE_RELATION, SHIFTED_RELATION)
    surfaces = (frozenset(), frozenset({SURFACE_PAIR}))
    for relation, surface_used in product(relations, surfaces):
        candidate = ClassifierPassage(
            source=classifier_state(relation=BASE_RELATION),
            target=classifier_state(relation=relation, surface_used=surface_used),
            recorded_rows=POLICY,
        )
        expected_delta = frozenset({SURFACE_PAIR}) if relation == SHIFTED_RELATION and surface_used else frozenset()
        assert classifier_surface_delta(candidate) == expected_delta
        assert classifier_shift(candidate) == (relation == SHIFTED_RELATION)

    assert classifier_surface_delta(passage(shifted=True)) == frozenset({SURFACE_PAIR})
    assert classifier_surface_delta(passage(shifted=False)) == frozenset()


def test_margin_stability_verifiable_exhaustive():
    """thm:philosophy-margin-stability-verifiable; Lean: BEDC.GroundCompiler.MetricsFlow.MetricCertificateFlow; primitive: metrics.classifier_certificate."""
    values = (0.0, 0.69, 0.70, 0.84, 0.85, 1.0)
    for r2, proxy in product(values, values):
        cert = classifier_certificate(
            {"linear_identifiability_r2": r2, "approx_identifiability_proxy": proxy}
        )
        assert cert["cert_status"] == (
            "certified" if r2 >= 0.85 and proxy >= 0.70 else "uncertified"
        )

    assert CERTIFIED["cert_status"] == "certified"
    assert UNCERTIFIED["cert_status"] == "uncertified"


def test_finite_ledger_coverage_verifiable_exhaustive():
    """thm:philosophy-finite-ledger-coverage-verifiable; Lean: BEDC.GroundCompiler.TheoremGenerated.LedgerSoundTheoremRecognition; primitive: ledger.ledger_gap."""
    required = (SOURCE_ROW, CLASSIFIER_ROW, STABILITY_ROW)
    for recorded in powerset(required):
        expected_gap = frozenset(required) - recorded
        assert ledger_gap(required, recorded) == expected_gap
        assert ledger_complete(required, recorded) == (expected_gap == frozenset())

    assert ledger_complete(required, frozenset(required))
    assert not ledger_complete(required, frozenset({SOURCE_ROW, CLASSIFIER_ROW}))


def test_open_semantics_not_closed_by_proof_alone_exhaustive():
    """thm:philosophy-open-semantics-not-closed-by-proof-alone; Lean: BEDC.GroundCompiler.SemanticMotif.MotifLedger; primitive: scope.semantic_rows."""
    cert = scoped_cert(certificate=SEMANTIC_CERTIFIED)
    claim = global_claim((cert,))
    semantic = semantic_rows(cert)
    assert semantic

    for recorded_semantic in powerset(semantic):
        recorded = global_required_rows(claim) - semantic | recorded_semantic
        candidate = global_claim((cert,), recorded_rows=recorded)
        assert globally_resolved(candidate) == (recorded_semantic == semantic)

    assert globally_resolved(claim)
    assert not globally_resolved(global_claim((cert,), recorded_rows=global_required_rows(claim) - semantic))


def test_empirical_stability_not_global_formal_stability_exhaustive():
    """thm:philosophy-empirical-stability-not-global-formal-stability; Lean: BEDC.GroundCompiler.NameCertGenerated.NameCertStabilitySoundnessEvent; primitive: hardening.fully_hardened_classifier."""
    critical = frozenset({STABILITY_ROW})
    for empirical, hardened, recorded in product((False, True), powerset(critical), powerset(critical)):
        profile = hardening_profile(
            required=critical,
            recorded=recorded,
            critical=critical,
            hardened=hardened,
            empirical=empirical,
        )
        expected = critical.issubset(recorded) and not critical_hardening_gap(profile, backend(critical))
        assert fully_hardened_classifier(profile, backend(critical)) == expected

    empirical_only = hardening_profile(required=critical, recorded=frozenset(), critical=critical, empirical=True)
    formal = hardening_profile(required=critical, recorded=critical, critical=critical, hardened=critical, empirical=True)
    assert empirical_only.empirical_stability and not fully_hardened_classifier(empirical_only, backend(critical))
    assert fully_hardened_classifier(formal, backend(critical))


def test_untranscribed_claims_no_proof_target_exhaustive():
    """thm:philosophy-untranscribed-claims-no-proof-target; Lean: BEDC.GroundCompiler.ImplementationInterface.CertificateLeanTargetSet; primitive: scope.verification_rows."""
    for status in ("unchecked", "kernel-checked", "failed"):
        cert = scoped_cert(certificate={**CERTIFIED, "verification_status": status})
        rows = verification_rows(cert)
        assert bool(rows) == (status == "kernel-checked")

    assert verification_rows(scoped_cert(certificate=KERNEL_CHECKED))
    assert not verification_rows(scoped_cert(certificate=CERTIFIED))


def test_verified_statement_needs_transcription_ledger_exhaustive():
    """thm:philosophy-verified-statement-needs-transcription-ledger; Lean: BEDC.GroundCompiler.SelfHostingCompilerFlow.GlobalVerificationSoundness; primitive: scope.verification_rows."""
    cert = scoped_cert(certificate=KERNEL_CHECKED)
    claim = global_claim((cert,))
    verification = verification_rows(cert)
    assert TRANSCRIPTION_ROW in verification

    for recorded_verification in powerset(verification):
        recorded = global_required_rows(claim) - verification | recorded_verification
        candidate = global_claim((cert,), recorded_rows=recorded)
        assert global_ledger_complete(candidate) == (recorded_verification == verification)

    assert global_ledger_complete(claim)
    assert not global_ledger_complete(global_claim((cert,), recorded_rows=global_required_rows(claim) - {TRANSCRIPTION_ROW}))


def test_transcription_gaps_block_full_hardening_exhaustive():
    """thm:philosophy-transcription-gaps-block-full-hardening; Lean: BEDC.GroundCompiler.AnalysisPipeline.CertificateObligationDischarge; primitive: hardening.critical_hardening_gap."""
    critical = frozenset({VERIFY_ROW, TRANSCRIPTION_ROW})
    hardener = backend(critical)
    for hardened, frontier, recorded in product(powerset(critical), powerset(critical), powerset(critical)):
        profile = hardening_profile(required=critical, recorded=recorded, critical=critical, hardened=hardened, frontier=frontier)
        expected_gap = critical - (hardened | frontier | recorded)
        assert critical_hardening_gap(profile, hardener) == expected_gap
        assert fully_hardened_classifier(profile, hardener) == (recorded == critical and not expected_gap)

    full = hardening_profile(required=critical, recorded=critical, critical=critical, hardened=critical)
    gap = hardening_profile(required=critical, recorded=frozenset({VERIFY_ROW}), critical=critical, hardened=frozenset({VERIFY_ROW}))
    assert fully_hardened_classifier(full, hardener)
    assert not fully_hardened_classifier(gap, hardener)


def test_verification_opacity_blocks_audit_completeness_exhaustive():
    """thm:philosophy-verification-opacity-blocks-audit-completeness; Lean: BEDC.GroundCompiler.SelfHostingReports.globalVerificationSound; primitive: scope.global_ledger_complete."""
    cert = scoped_cert(certificate=KERNEL_CHECKED)
    claim = global_claim((cert,))
    verification = verification_rows(cert)

    for recorded_verification in powerset(verification):
        recorded = global_required_rows(claim) - verification | recorded_verification
        candidate = global_claim((cert,), recorded_rows=recorded)
        assert globally_resolved(candidate) == (recorded_verification == verification)

    opaque = global_claim((cert,), recorded_rows=global_required_rows(claim) - {next(iter(verification))})
    assert globally_resolved(claim)
    assert not globally_resolved(opaque)


def test_component_verification_ledger_not_explanation_ledger_exhaustive():
    """thm:philosophy-component-verification-ledger-not-explanation-ledger; Lean: BEDC.GroundCompiler.ChapterFlow.LedgerSound; primitive: scope.scope_rows and scope.verification_rows."""
    cert = scoped_cert(certificate=KERNEL_CHECKED)
    explanation = scope_rows(cert.scope)
    verification = verification_rows(cert)
    assert explanation.isdisjoint(verification)

    for explanation_rows, verification_subset in product(powerset(explanation), powerset(verification)):
        scoped = scoped_cert(certificate=KERNEL_CHECKED, recorded_rows=explanation_rows)
        claim = global_claim((scoped,), recorded_rows=verification_subset | explanation_rows)
        if verification_subset == verification:
            assert scoped_resolved(scoped) == explanation.issubset(explanation_rows)
        assert not globally_resolved(claim)

    assert scoped_resolved(cert)
    assert not scoped_resolved(scoped_cert(certificate=KERNEL_CHECKED, recorded_rows=frozenset()))


def test_partial_verification_not_scoped_full_exhaustive():
    """thm:philosophy-partial-verification-not-scoped-full; Lean: BEDC.GroundCompiler.AnalysisPipeline.CertificateObligationDischarge; primitive: hardening.partially_hardened_classifier."""
    critical = frozenset({SOURCE_ROW, CLASSIFIER_ROW, STABILITY_ROW})
    hardener = backend(critical)
    for hardened in powerset(critical):
        profile = hardening_profile(required=critical, recorded=hardened, critical=critical, hardened=hardened)
        assert partially_hardened_classifier(profile) == (bool(hardened) and bool(critical - hardened))
        assert fully_hardened_classifier(profile, hardener) == (hardened == critical)

    partial = hardening_profile(required=critical, recorded=frozenset({SOURCE_ROW}), critical=critical, hardened=frozenset({SOURCE_ROW}))
    full = hardening_profile(required=critical, recorded=critical, critical=critical, hardened=critical)
    assert partially_hardened_classifier(partial) and not fully_hardened_classifier(partial, hardener)
    assert fully_hardened_classifier(full, hardener)


def test_global_verification_requires_global_scope_ledger_exhaustive():
    """thm:philosophy-global-verification-requires-global-scope-ledger; Lean: BEDC.GroundCompiler.SelfHostingCompilerFlow.GlobalVerificationFlow; primitive: scope.global_required_rows."""
    cert = scoped_cert(certificate=KERNEL_CHECKED)
    claim = global_claim((cert,), behavior_family=frozenset({"B"}))
    required = global_required_rows(claim)

    for recorded in powerset(required):
        candidate = global_claim((cert,), behavior_family=frozenset({"B"}), recorded_rows=recorded)
        assert globally_resolved(candidate) == required.issubset(recorded)

    scoped_only = global_claim((cert,), recorded_rows=cert.recorded_rows | verification_rows(cert))
    assert globally_resolved(claim)
    assert not globally_resolved(scoped_only)


def test_one_hardened_ndna_locus_not_all_ndna_exhaustive():
    """thm:philosophy-one-hardened-ndna-locus-not-all-ndna; Lean: BEDC.GroundCompiler.NameCertGenerated.CompleteFiveFieldRecognition; primitive: discovery.ndna_positive_criterion."""
    for complete, anchored, compatible, ledgered in product((False, True), repeat=4):
        candidate = discovery_claim(
            ndna_complete=complete,
            ndna_anchored=anchored,
            ndna_namecert_compatible=compatible,
            ndna_ledger_complete=ledgered,
            ndna_net=1.0,
        )
        assert discovery.ndna_positive_criterion(candidate) == (
            discovery.certified_discovery(candidate)
            and discovery.positive_information(candidate)
            and discovery.protocol_complete(candidate)
            and discovery.protocol_scope_complete(candidate)
            and discovery.debt_complete(candidate)
            and classifier_shift(candidate.passage)
            and complete
            and anchored
            and compatible
            and ledgered
            and candidate.ndna_net_information > 0.0
            and not candidate.laundering_modes
        )

    one_locus = discovery_claim(ndna_complete=True, ndna_anchored=False, ndna_namecert_compatible=False, ndna_ledger_complete=False, ndna_net=1.0)
    full_profile = discovery_claim(ndna_complete=True, ndna_anchored=True, ndna_namecert_compatible=True, ndna_ledger_complete=True, ndna_net=1.0)
    assert not discovery.ndna_positive_criterion(one_locus)
    assert discovery.ndna_positive_criterion(full_profile)


def test_fully_verified_ndna_requires_profile_exhaustive():
    """thm:philosophy-fully-verified-ndna-requires-profile; Lean: BEDC.GroundCompiler.SelfHostingCompilerFlow.GlobalStatusCertificateFlow; primitive: discovery.strong_positive_discovery."""
    for reproducible, complete, anchored, compatible, ledgered in product((False, True), repeat=5):
        candidate = discovery_claim(
            reproducible=reproducible,
            ndna_complete=complete,
            ndna_anchored=anchored,
            ndna_namecert_compatible=compatible,
            ndna_ledger_complete=ledgered,
        )
        expected = (
            discovery.positive_discovery(candidate)
            and discovery.critical_debt_free(candidate)
            and reproducible
            and complete
            and anchored
            and compatible
            and ledgered
        )
        assert discovery.strong_positive_discovery(candidate) == expected

    full = discovery_claim(reproducible=True, ndna_complete=True, ndna_anchored=True, ndna_namecert_compatible=True, ndna_ledger_complete=True)
    missing_profile = discovery_claim(reproducible=True, ndna_complete=True, ndna_anchored=True, ndna_namecert_compatible=False, ndna_ledger_complete=True)
    assert discovery.strong_positive_discovery(full)
    assert not discovery.strong_positive_discovery(missing_profile)


def test_verification_gain_not_classifier_novelty_exhaustive():
    """thm:philosophy-verification-gain-not-classifier-novelty; Lean: BEDC.GroundCompiler.NameCertGenerated.NameCertClassifierSoundnessEvent; primitive: discovery.verification_assisted_positive_discovery."""
    for shifted, assisted, benefit in product((False, True), (False, True), (0.0, 1.0)):
        candidate = discovery_claim(
            shifted=shifted,
            benefit={"verification": benefit},
            verification_assisted=assisted,
            verification_benefit=benefit,
        )
        if discovery.verification_assisted_positive_discovery(candidate):
            assert classifier_shift(candidate.passage)

    verification_only = discovery_claim(shifted=False, benefit={"verification": 1.0}, verification_assisted=True, verification_benefit=1.0)
    assisted = discovery_claim(benefit={"verification": 1.0}, verification_assisted=True, verification_benefit=1.0)
    assert not discovery.verification_assisted_positive_discovery(verification_only)
    assert discovery.verification_assisted_positive_discovery(assisted)


def test_verification_assisted_discovery_counts_cost_exhaustive():
    """thm:philosophy-verification-assisted-discovery-counts-cost; Lean: BEDC.GroundCompiler.ImplementationInterface.CertificateLeanTargetSet; primitive: discovery.verification_cost_counted."""
    for cost_counted, row_counted in product((False, True), repeat=2):
        candidate = discovery_claim(
            benefit={"verification": 1.0},
            score={"verification-cost": 0.1} if cost_counted else {"classifier": 0.1},
            verification_assisted=True,
            verification_benefit=0.8,
            verification_required=frozenset({VERIFY_ROW}),
            verification_recorded=frozenset({VERIFY_ROW}) if row_counted else frozenset(),
        )
        assert discovery.verification_cost_counted(candidate) == (cost_counted and row_counted)

    counted = discovery_claim(benefit={"verification": 1.0}, score={"verification-cost": 0.1}, verification_assisted=True, verification_benefit=0.8, verification_required=frozenset({VERIFY_ROW}), verification_recorded=frozenset({VERIFY_ROW}))
    uncounted = discovery_claim(benefit={"verification": 1.0}, verification_assisted=True, verification_benefit=0.8, verification_required=frozenset({VERIFY_ROW}))
    assert discovery.verification_cost_counted(counted)
    assert not discovery.verification_cost_counted(uncounted)


def test_verification_misuse_invalidates_claim_exhaustive():
    """thm:philosophy-verification-misuse-invalidates-claim; Lean: BEDC.GroundCompiler.AnalysisPipeline.LedgerAuditFailureKind.missingLedger; primitive: discovery.laundering_invalidates."""
    modes = ("verification", "proof-quantity", "backend", "scope")
    for active_modes in powerset(modes):
        candidate = discovery_claim(laundering=active_modes)
        assert discovery.laundering_invalidates(candidate) == bool(active_modes)
        if active_modes:
            assert not discovery.positive_discovery(candidate)

    clean = discovery_claim()
    laundered = discovery_claim(laundering=frozenset({"backend"}))
    assert discovery.positive_discovery(clean)
    assert discovery.laundering_invalidates(laundered)


def test_formal_verification_certified_interpretability_theorem_exhaustive():
    """thm:philosophy-formal-verification-certified-interpretability-theorem; Lean: BEDC.GroundCompiler.SelfHostingCompilerFlow.GlobalVerificationSoundness; primitive: discovery.capstone_positive_interpretability_discovery."""
    verification = frozenset({VERIFY_ROW})
    hardener = backend(frozenset({CLASSIFIER_ROW, VERIFY_ROW}))
    profile = hardening_profile(
        required=frozenset({CLASSIFIER_ROW, VERIFY_ROW}),
        recorded=frozenset({CLASSIFIER_ROW, VERIFY_ROW}),
        critical=frozenset({CLASSIFIER_ROW, VERIFY_ROW}),
        hardened=frozenset({CLASSIFIER_ROW, VERIFY_ROW}),
    )
    assert fully_hardened_classifier(profile, hardener)

    for shifted, passage_rows, cost_counted, misuse in product(
        (False, True),
        powerset((CLASSIFIER_ROW,)),
        (False, True),
        (False, True),
    ):
        candidate = discovery_claim(
            shifted=shifted,
            passage_rows=passage_rows,
            claim_rows=passage_rows,
            benefit={"coverage": 1.0, "verification": 0.5},
            score={"verification-cost": 0.1} if cost_counted else {"classifier": 0.1},
            verification_assisted=True,
            verification_benefit=0.5,
            verification_required=verification,
            verification_recorded=verification if cost_counted else frozenset(),
            hardening=profile,
            hardening_backend=hardener,
            laundering=frozenset({"backend"}) if misuse else frozenset(),
        )
        expected = (
            discovery.positive_discovery(candidate)
            and discovery.certified_discovery(candidate)
            and classifier_shift(candidate.passage)
            and ledger_complete(candidate.ledger_required_rows, candidate.ledger_recorded_rows)
            and discovery.protocol_complete(candidate)
            and discovery.protocol_scope_complete(candidate)
            and discovery.debt_complete(candidate)
            and not discovery.laundering_invalidates(candidate)
            and fully_hardened_classifier(profile, hardener)
            and discovery.net_information(candidate) > 0.0
        )
        assert discovery.capstone_positive_interpretability_discovery(candidate) == expected
        assert discovery.verification_cost_counted(candidate) == cost_counted

    positive = discovery_claim(
        benefit={"coverage": 1.0, "verification": 0.5},
        score={"verification-cost": 0.1},
        verification_assisted=True,
        verification_benefit=0.5,
        verification_required=verification,
        verification_recorded=verification,
        hardening=profile,
        hardening_backend=hardener,
    )
    counter = discovery_claim(shifted=False, benefit={"verification": 1.0})
    assert discovery.capstone_positive_interpretability_discovery(positive)
    assert not discovery.capstone_positive_interpretability_discovery(counter)
    assert structural_discovery(positive.passage)
    assert shift_information(positive.passage) == 1
    assert not ledger_only_classifier(profile)
