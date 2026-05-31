from itertools import combinations, product

from bedc_quality_lab import discovery
from bedc_quality_lab.classifier_shift import ClassifierPassage, ClassifierState, classifier_shift
from bedc_quality_lab.hardening import HardeningBackend, HardeningProfile, fully_hardened_classifier
from bedc_quality_lab.ledger import LedgerRowKey, ledger_complete
from bedc_quality_lab.metrics import classifier_certificate
from bedc_quality_lab.scope import GlobalResolutionClaim, Scope, ScopedCertificate, global_required_rows, scope_rows, scoped_resolved


SOURCE_IDS = frozenset({"a", "b"})
SHIFT_ROW = LedgerRowKey("classifier", "a->b")
SCOPE_ROW = LedgerRowKey("scope", "public")
VERIFY_ROW = LedgerRowKey("verification", "cost")
POLICY = frozenset({SHIFT_ROW})
BASE_RELATION = frozenset({("a", "a", "same"), ("a", "b", "near"), ("b", "b", "same")})
SHIFTED_RELATION = frozenset({("a", "a", "same"), ("a", "b", "far"), ("b", "b", "same")})
CERTIFIED = classifier_certificate({"linear_identifiability_r2": 0.95, "approx_identifiability_proxy": 0.90})
UNCERTIFIED = classifier_certificate({"linear_identifiability_r2": 0.10, "approx_identifiability_proxy": 0.10})


def powerset(rows):
    rows = tuple(rows)
    for size in range(len(rows) + 1):
        for members in combinations(rows, size):
            yield frozenset(members)


def state(*, shifted=True, certificate=CERTIFIED, surface=frozenset({("a", "b")})):
    return ClassifierState(
        source_ids=SOURCE_IDS,
        pattern_id="finite-positive-discovery",
        ledger_policy=POLICY,
        relation=SHIFTED_RELATION if shifted else BASE_RELATION,
        certificate=certificate,
        surface_used=surface,
    )


def passage(*, shifted=True, certificate=CERTIFIED, recorded_rows=POLICY, surface=frozenset({("a", "b")})):
    return ClassifierPassage(
        source=state(shifted=False),
        target=state(shifted=shifted, certificate=certificate, surface=surface),
        recorded_rows=recorded_rows,
    )


def scoped_cert(*, certificate=CERTIFIED, recorded_rows=None, boundary=frozenset({"outside-scope"})):
    scope = Scope(
        domain_ids=frozenset({"D0"}),
        model_id="M",
        admitted_family_id="A",
        behavior_id="B",
    )
    required = scope_rows(scope)
    return ScopedCertificate(
        scope=scope,
        classifier_id="C",
        namecert_id="N",
        required_rows=required,
        recorded_rows=required if recorded_rows is None else recorded_rows,
        certificate=certificate,
        not_claimed_boundary=boundary,
    )


def global_resolution_claim(*, recorded_rows=None):
    cert = scoped_cert()
    base = GlobalResolutionClaim(
        model_id="M",
        behavior_family=frozenset({"B"}),
        certificates=(cert,),
        global_recorded_rows=frozenset(),
    )
    rows = global_required_rows(base) if recorded_rows is None else recorded_rows
    return GlobalResolutionClaim(
        model_id=base.model_id,
        behavior_family=base.behavior_family,
        certificates=base.certificates,
        global_recorded_rows=rows,
    )


def hardening_profile(*, critical_rows=frozenset(), hardened_rows=frozenset(), recorded_rows=frozenset()):
    return HardeningProfile(
        certificate=CERTIFIED,
        mode_rows=frozenset(),
        declared_mode_rows=frozenset(),
        open_mode_rows=frozenset(),
        ledger_required_rows=critical_rows,
        ledger_recorded_rows=recorded_rows,
        critical_rows=critical_rows,
        hardened_rows=hardened_rows,
        frontier_rows=frozenset(),
        non_hardenable_residue=frozenset(),
    )


def claim(
    *,
    shifted=True,
    certificate=CERTIFIED,
    passage_rows=POLICY,
    claim_rows=POLICY,
    required_rows=POLICY,
    benefit=None,
    score=None,
    debt=None,
    public=True,
    scope_sealed=True,
    boundary=frozenset({"outside-scope"}),
    witness=True,
    weights_public=True,
    source_public=True,
    target_public=True,
    modes=frozenset({"coverage"}),
    omitted=None,
    scoped=True,
    scoped_certificate=None,
    critical_debt_rows=frozenset(),
    reproducible=False,
    ndna_complete=False,
    ndna_anchored=False,
    ndna_namecert_compatible=False,
    ndna_ledger_complete=False,
    ndna_net=0.0,
    black_box_debt_reduction=0.0,
    black_box_score_cost=0.0,
    verification_assisted=False,
    verification_benefit=0.0,
    verification_required_rows=frozenset(),
    verification_recorded_rows=frozenset(),
    laundering=frozenset(),
    hardening=None,
    backend=None,
    global_claim=None,
):
    cert = scoped_certificate
    if scoped and cert is None:
        cert = scoped_cert(certificate=certificate, boundary=boundary)
    return discovery.DiscoveryClaim(
        passage=passage(shifted=shifted, certificate=certificate, recorded_rows=passage_rows),
        benefit_terms={"coverage": 1.0} if benefit is None else benefit,
        score_terms={"classifier": 0.10} if score is None else score,
        debt_terms={"ledger": 0.10} if debt is None else debt,
        ledger_required_rows=required_rows,
        ledger_recorded_rows=claim_rows,
        public_cost_protocol=public,
        scope_sealed=scope_sealed,
        not_claimed_boundary=boundary,
        local_or_formal_witness=witness,
        weight_profile_public=weights_public,
        source_scope_public=source_public,
        target_scope_public=target_public,
        benefit_modes=modes,
        omitted_debt_terms={} if omitted is None else omitted,
        scoped_certificate=cert,
        global_claim=global_claim,
        critical_debt_rows=critical_debt_rows,
        reproducible_evidence=reproducible,
        ndna_complete=ndna_complete,
        ndna_anchored=ndna_anchored,
        ndna_namecert_compatible=ndna_namecert_compatible,
        ndna_ledger_complete=ndna_ledger_complete,
        ndna_net_information=ndna_net,
        black_box_debt_reduction=black_box_debt_reduction,
        black_box_score_cost=black_box_score_cost,
        verification_assisted=verification_assisted,
        verification_benefit=verification_benefit,
        verification_required_rows=verification_required_rows,
        verification_recorded_rows=verification_recorded_rows,
        laundering_modes=laundering,
        hardening_profile=hardening,
        hardening_backend=backend,
    )


def test_philosophy_positive_discovery_implies_certified_discovery_exhaustive():
    """thm:philosophy-positive-discovery-implies-certified-discovery; Lean: BEDC.GroundCompiler.NameCertGenerated.LedgerCompleteNameCertFlow and BEDC.GroundCompiler.AnalysisPipeline.StageBridgeObligationDiscovery."""
    for shifted, certificate, rows, boundary, net in product(
        (False, True), (UNCERTIFIED, CERTIFIED), powerset((SHIFT_ROW,)), (frozenset(), frozenset({"outside"})), (-0.2, 0.8)
    ):
        candidate = claim(shifted=shifted, certificate=certificate, passage_rows=rows, claim_rows=rows, boundary=boundary, benefit={"coverage": net + 0.2})
        if discovery.positive_discovery(candidate):
            assert discovery.certified_discovery(candidate)
    positive = claim()
    counter = claim(shifted=False)
    assert discovery.positive_discovery(positive) and discovery.certified_discovery(positive)
    assert not discovery.positive_discovery(counter) and not discovery.certified_discovery(counter)


def test_philosophy_classifier_novelty_alone_not_positive_discovery_exhaustive():
    """thm:philosophy-classifier-novelty-alone-not-positive-discovery; Lean: BEDC.GroundCompiler.NameCertGenerated.NameCertClassifierSoundnessEvent and BEDC.GroundCompiler.ChapterFlow.LedgerSound."""
    for certificate, rows, net, public in product((UNCERTIFIED, CERTIFIED), powerset((SHIFT_ROW,)), (-0.3, 0.8), (False, True)):
        candidate = claim(certificate=certificate, passage_rows=rows, claim_rows=rows, benefit={"coverage": net + 0.2}, public=public)
        if classifier_shift(candidate.passage) and not discovery.positive_discovery(candidate):
            assert not discovery.capstone_positive_interpretability_discovery(candidate)
    positive = claim()
    novelty_only = claim(certificate=UNCERTIFIED, passage_rows=frozenset(), claim_rows=frozenset())
    assert classifier_shift(novelty_only.passage) and not discovery.positive_discovery(novelty_only)
    assert discovery.positive_discovery(positive)


def test_philosophy_positive_information_alone_not_discovery_exhaustive():
    """thm:philosophy-positive-information-alone-not-discovery; Lean: BEDC.GroundCompiler.MetricsFlow.QualityMetricEnvelope and BEDC.GroundCompiler.NameCertGenerated.NameCertRecognitionRelation."""
    for shifted, benefit in product((False, True), (0.0, 1.0, 2.0)):
        candidate = claim(shifted=shifted, benefit={"ledger": benefit})
        if discovery.positive_information(candidate) and not classifier_shift(candidate.passage):
            assert not discovery.positive_discovery(candidate)
    positive = claim()
    info_only = claim(shifted=False, benefit={"ledger": 2.0})
    assert discovery.positive_information(info_only) and not discovery.positive_discovery(info_only)
    assert discovery.positive_discovery(positive)


def test_philosophy_ledger_completion_positive_not_discovery_exhaustive():
    """thm:philosophy-ledger-completion-positive-not-discovery; Lean: BEDC.GroundCompiler.AnalysisPipeline.LedgerAuditFailureKind.motifWithoutLedger and BEDC.GroundCompiler.NameCertGenerated.namecert_without_ledger_not_admissible."""
    for rows, benefit in product(powerset((SHIFT_ROW,)), (0.0, 1.0, 2.0)):
        candidate = claim(shifted=False, passage_rows=rows, claim_rows=rows, benefit={"ledger": benefit})
        if discovery.ledger_completion(candidate) and discovery.positive_information(candidate):
            assert not discovery.positive_discovery(candidate)
    positive = claim()
    ledger_positive = claim(shifted=False, benefit={"ledger": 2.0})
    assert discovery.ledger_completion(ledger_positive) and not discovery.positive_discovery(ledger_positive)
    assert discovery.positive_discovery(positive)


def test_philosophy_formal_hardening_positive_not_discovery_exhaustive():
    """thm:philosophy-formal-hardening-positive-not-discovery; Lean: BEDC.GroundCompiler.AnalysisPipeline.CertificateObligationDischarge and BEDC.GroundCompiler.SelfHostingCompilerFlow.GlobalVerificationSoundness."""
    backend = HardeningBackend("lean", frozenset({VERIFY_ROW}))
    for hardened_rows, benefit in product(powerset((VERIFY_ROW,)), (0.0, 2.0)):
        profile = hardening_profile(critical_rows=frozenset({VERIFY_ROW}), hardened_rows=hardened_rows, recorded_rows=frozenset({VERIFY_ROW}))
        candidate = claim(shifted=False, benefit={"verification": benefit}, hardening=profile, backend=backend)
        if benefit > 0.2 and fully_hardened_classifier(profile, backend):
            assert discovery.positive_information(candidate) and not discovery.positive_discovery(candidate)
    positive = claim()
    hardening_only = claim(shifted=False, benefit={"verification": 2.0}, hardening=hardening_profile(), backend=backend)
    assert discovery.positive_information(hardening_only) and not discovery.positive_discovery(hardening_only)
    assert discovery.positive_discovery(positive)


def test_philosophy_positive_discovery_requires_protocol_completeness_exhaustive():
    """thm:philosophy-positive-discovery-requires-protocol-completeness; Lean: BEDC.GroundCompiler.ImplementationInterface.CertificateRecognizerModules and BEDC.GroundCompiler.AnalysisPipeline.StageLedgerAudit."""
    for public, weights, source, target, boundary in product((False, True), repeat=5):
        candidate = claim(public=public, weights_public=weights, source_public=source, target_public=target, boundary=frozenset({"outside"}) if boundary else frozenset())
        if discovery.positive_discovery(candidate):
            assert discovery.protocol_complete(candidate)
    positive = claim()
    opaque = claim(public=False)
    assert discovery.protocol_complete(positive) and discovery.positive_discovery(positive)
    assert not discovery.protocol_complete(opaque) and not discovery.positive_discovery(opaque)


def test_philosophy_cost_debt_can_invalidate_positivity_exhaustive():
    """thm:philosophy-cost-debt-can-invalidate-positivity; Lean: BEDC.GroundCompiler.MetricsFlow.MetricCertificateFlow and BEDC.GroundCompiler.AnalysisPipeline.LedgerAuditFailureKind.missingLedger."""
    for omitted in (0.0, 0.4, 1.0):
        candidate = claim(benefit={"coverage": 0.6}, omitted={"verification": omitted} if omitted else {})
        expected_net = 0.6 - 0.1 - 0.1 - omitted
        assert discovery.net_information(candidate) == expected_net
        assert discovery.positive_information(candidate) == (expected_net > 0.0)
    positive = claim(benefit={"coverage": 0.6})
    invalidated = claim(benefit={"coverage": 0.6}, omitted={"verification": 1.0})
    assert discovery.positive_discovery(positive)
    assert discovery.apparent_net_information(invalidated) > 0.0 and not discovery.positive_discovery(invalidated)


def test_philosophy_positive_benefit_modes_overlap_exhaustive():
    """thm:philosophy-positive-benefit-modes-overlap; Lean: BEDC.GroundCompiler.MetricsFlow.MetricClaimKind.positiveReuseDepthImpliesReuseCertificate and BEDC.GroundCompiler.SemanticMotif.LedgerCompressionMotif."""
    modes = ("coverage", "prediction", "transfer")
    for active in powerset(modes):
        benefit = {mode: (0.5 if mode in active else 0.0) for mode in modes}
        candidate = claim(benefit=benefit, modes=frozenset(modes))
        assert discovery.benefit_modes_overlap(candidate) == (discovery.positive_discovery(candidate) and len(active) > 1)
    overlap = claim(benefit={"coverage": 0.5, "transfer": 0.5}, modes=frozenset({"coverage", "transfer"}))
    single = claim(benefit={"coverage": 1.0}, modes=frozenset({"coverage"}))
    assert discovery.benefit_modes_overlap(overlap)
    assert not discovery.benefit_modes_overlap(single)


def test_philosophy_ndna_positive_criterion_implies_positive_discovery_exhaustive():
    """thm:philosophy-ndna-positive-criterion-implies-positive-discovery; Lean: BEDC.GroundCompiler.NameCertGenerated.CompleteFiveFieldRecognition and BEDC.GroundCompiler.NameCertGenerated.LedgerCompleteNameCertFlow."""
    for complete, anchored, compatible, ledgered, ndna_net in product((False, True), repeat=5):
        candidate = claim(
            ndna_complete=complete,
            ndna_anchored=anchored,
            ndna_namecert_compatible=compatible,
            ndna_ledger_complete=ledgered,
            ndna_net=1.0 if ndna_net else 0.0,
        )
        if discovery.ndna_positive_criterion(candidate):
            assert discovery.positive_discovery(candidate)
    ndna = claim(ndna_complete=True, ndna_anchored=True, ndna_namecert_compatible=True, ndna_ledger_complete=True, ndna_net=1.0)
    incomplete = claim(ndna_complete=True, ndna_anchored=True, ndna_namecert_compatible=True, ndna_ledger_complete=False, ndna_net=1.0)
    assert discovery.ndna_positive_criterion(ndna) and discovery.positive_discovery(ndna)
    assert not discovery.ndna_positive_criterion(incomplete)


def test_philosophy_ndna_completeness_alone_not_positive_discovery_exhaustive():
    """thm:philosophy-ndna-completeness-alone-not-positive-discovery; Lean: BEDC.GroundCompiler.NameCertGenerated.NameCertFlow and BEDC.GroundCompiler.AnalysisPipeline.AnalysisEvidenceKind.nameCertFlow."""
    for shifted, compatible, ndna_net in product((False, True), (False, True), (0.0, 1.0)):
        candidate = claim(shifted=shifted, ndna_complete=True, ndna_anchored=True, ndna_namecert_compatible=compatible, ndna_ledger_complete=True, ndna_net=ndna_net)
        if candidate.ndna_complete and not discovery.ndna_positive_criterion(candidate):
            assert not discovery.capstone_positive_interpretability_discovery(candidate) or discovery.positive_discovery(candidate)
    positive = claim()
    completeness_only = claim(shifted=False, ndna_complete=True)
    assert completeness_only.ndna_complete and not discovery.positive_discovery(completeness_only)
    assert discovery.positive_discovery(positive)


def test_philosophy_strong_positive_implies_positive_exhaustive():
    """thm:philosophy-strong-positive-implies-positive; Lean: BEDC.GroundCompiler.SelfHostingCompilerFlow.GlobalStatusCertificateFlow and BEDC.GroundCompiler.AnalysisPipeline.CertificateObligationDischarge."""
    for reproducible, critical_debt, ndna_ok in product((False, True), repeat=3):
        candidate = claim(
            reproducible=reproducible,
            critical_debt_rows=frozenset({SCOPE_ROW}) if critical_debt else frozenset(),
            ndna_complete=ndna_ok,
            ndna_anchored=ndna_ok,
            ndna_namecert_compatible=ndna_ok,
            ndna_ledger_complete=ndna_ok,
        )
        if discovery.strong_positive_discovery(candidate):
            assert discovery.positive_discovery(candidate)
    strong = claim(reproducible=True, ndna_complete=True, ndna_anchored=True, ndna_namecert_compatible=True, ndna_ledger_complete=True)
    weak = claim()
    assert discovery.strong_positive_discovery(strong) and discovery.positive_discovery(strong)
    assert not discovery.strong_positive_discovery(weak) and discovery.positive_discovery(weak)


def test_philosophy_positive_need_not_be_strong_exhaustive():
    """thm:philosophy-positive-need-not-be-strong; Lean: BEDC.GroundCompiler.AnalysisPipeline.StageBridgeObligationDiscovery and BEDC.GroundCompiler.SelfHostingCompilerFlow.GlobalVerificationSoundness."""
    for reproducible, critical_debt in product((False, True), repeat=2):
        candidate = claim(reproducible=reproducible, critical_debt_rows=frozenset({SCOPE_ROW}) if critical_debt else frozenset())
        if discovery.positive_discovery(candidate) and not reproducible:
            assert not discovery.strong_positive_discovery(candidate)
    strong = claim(reproducible=True, ndna_complete=True, ndna_anchored=True, ndna_namecert_compatible=True, ndna_ledger_complete=True)
    weak = claim()
    assert discovery.positive_discovery(weak) and not discovery.strong_positive_discovery(weak)
    assert discovery.strong_positive_discovery(strong)


def test_philosophy_positive_black_box_resolution_not_discovery_exhaustive():
    """thm:philosophy-positive-black-box-resolution-not-discovery; Lean: BEDC.GroundCompiler.SelfHostingReports.P9ReportFlow.selfHostingLedger and BEDC.GroundCompiler.AnalysisPipeline.StageLedgerAudit."""
    for shifted, reduction, cost in product((False, True), (0.0, 1.0), (0.2, 1.2)):
        candidate = claim(shifted=shifted, black_box_debt_reduction=reduction, black_box_score_cost=cost)
        if discovery.positive_black_box_resolution(candidate) and not classifier_shift(candidate.passage):
            assert not discovery.positive_discovery(candidate)
    resolution_only = claim(shifted=False, black_box_debt_reduction=1.0, black_box_score_cost=0.2, benefit={"ledger": 1.0})
    discovery_resolution = claim(black_box_debt_reduction=1.0, black_box_score_cost=0.2)
    assert discovery.positive_black_box_resolution(resolution_only) and not discovery.positive_discovery(resolution_only)
    assert discovery.positive_discovery_resolution(discovery_resolution)


def test_philosophy_positive_discovery_resolution_strongest_exhaustive():
    """thm:philosophy-positive-discovery-resolution-strongest; Lean: BEDC.GroundCompiler.ChapterFlow.CertificateSound and BEDC.GroundCompiler.SelfHostingCompilerFlow.GlobalVerificationFlow."""
    for positive_axis, resolution_axis in product((False, True), repeat=2):
        candidate = claim(
            shifted=positive_axis,
            black_box_debt_reduction=1.0 if resolution_axis else 0.0,
            black_box_score_cost=0.2,
            benefit={"coverage": 1.0},
        )
        assert discovery.positive_discovery_resolution(candidate) == (discovery.positive_discovery(candidate) and discovery.positive_black_box_resolution(candidate))
    strongest = claim(black_box_debt_reduction=1.0, black_box_score_cost=0.2)
    missing_resolution = claim(black_box_debt_reduction=0.0, black_box_score_cost=0.2)
    assert discovery.positive_discovery_resolution(strongest)
    assert discovery.positive_discovery(missing_resolution) and not discovery.positive_discovery_resolution(missing_resolution)


def test_philosophy_verification_assistance_not_replace_novelty_exhaustive():
    """thm:philosophy-verification-assistance-not-replace-novelty; Lean: BEDC.GroundCompiler.AnalysisPipeline.CertificateObligationDischarge and BEDC.GroundCompiler.NameCertGenerated.NameCertClassifierSoundnessEvent."""
    for shifted, assisted, benefit in product((False, True), (False, True), (0.0, 1.0)):
        candidate = claim(shifted=shifted, benefit={"verification": benefit}, verification_assisted=assisted, verification_benefit=benefit)
        if discovery.verification_assisted_positive_discovery(candidate):
            assert classifier_shift(candidate.passage)
    assisted = claim(verification_assisted=True, verification_benefit=0.5, benefit={"verification": 1.0})
    verify_only = claim(shifted=False, verification_assisted=True, verification_benefit=1.0, benefit={"verification": 1.0})
    assert discovery.verification_assisted_positive_discovery(assisted)
    assert not discovery.verification_assisted_positive_discovery(verify_only)


def test_philosophy_verification_dependent_assistance_truth_table_exhaustive():
    """thm:philosophy-verification-assistance-not-replace-novelty; Lean: BEDC.GroundCompiler.AnalysisPipeline.CertificateObligationDischarge and BEDC.GroundCompiler.NameCertGenerated.NameCertClassifierSoundnessEvent."""
    for assisted, verification_benefit, total_benefit in product((False, True), (0.0, 0.4, 1.0), (0.4, 0.8, 1.4)):
        candidate = claim(
            verification_assisted=assisted,
            verification_benefit=verification_benefit,
            benefit={"verification": total_benefit},
        )
        assert discovery.verification_dependent(candidate) == (
            discovery.verification_assisted_positive_discovery(candidate)
            and discovery.net_information(candidate) - candidate.verification_benefit <= 0.0
        )
    dependent = claim(verification_assisted=True, verification_benefit=0.9, benefit={"verification": 1.0})
    independent = claim(verification_assisted=True, verification_benefit=0.2, benefit={"verification": 1.0})
    unassisted = claim(verification_assisted=False, verification_benefit=0.9, benefit={"verification": 1.0})
    assert discovery.verification_dependent(dependent)
    assert not discovery.verification_dependent(independent)
    assert not discovery.verification_dependent(unassisted)


def test_philosophy_verification_assisted_counts_cost_exhaustive():
    """thm:philosophy-verification-assisted-counts-cost; Lean: BEDC.GroundCompiler.ImplementationInterface.CertificateLeanTargetSet and BEDC.GroundCompiler.AnalysisPipeline.CertificateObligationDischarge."""
    for cost_counted, row_counted in product((False, True), repeat=2):
        candidate = claim(
            benefit={"verification": 1.0},
            score={"verification-cost": 0.1} if cost_counted else {"classifier": 0.1},
            verification_assisted=True,
            verification_benefit=0.6,
            verification_required_rows=frozenset({VERIFY_ROW}),
            verification_recorded_rows=frozenset({VERIFY_ROW}) if row_counted else frozenset(),
        )
        assert discovery.verification_cost_counted(candidate) == (cost_counted and row_counted)
    counted = claim(benefit={"verification": 1.0}, score={"verification-cost": 0.1}, verification_assisted=True, verification_benefit=0.6, verification_required_rows=frozenset({VERIFY_ROW}), verification_recorded_rows=frozenset({VERIFY_ROW}))
    uncounted = claim(benefit={"verification": 1.0}, verification_assisted=True, verification_benefit=0.6, verification_required_rows=frozenset({VERIFY_ROW}), verification_recorded_rows=frozenset())
    assert discovery.verification_cost_counted(counted)
    assert not discovery.verification_cost_counted(uncounted)


def test_philosophy_global_resolution_protocol_scope_complete_exhaustive():
    """thm:philosophy-global-resolution-requires-global-ledger-principle; Lean: BEDC.GroundCompiler.SelfHostingCompilerFlow.GlobalVerificationFlow and BEDC.GroundCompiler.SelfHostingCompilerFlow.GlobalStatusCertificateFlow."""
    full = global_resolution_claim()
    required = global_required_rows(full)
    for recorded_rows in powerset(required):
        global_claim = global_resolution_claim(recorded_rows=recorded_rows)
        candidate = claim(scoped=False, global_claim=global_claim)
        assert discovery.protocol_scope_complete(candidate) == required.issubset(recorded_rows)
    resolved = claim(scoped=False, global_claim=full)
    incomplete = claim(scoped=False, global_claim=global_resolution_claim(recorded_rows=frozenset(tuple(required)[1:])))
    unsealed = claim(scoped=False, scope_sealed=False, global_claim=full)
    assert discovery.protocol_scope_complete(resolved)
    assert not discovery.protocol_scope_complete(incomplete)
    assert not discovery.protocol_scope_complete(unsealed)


def test_philosophy_discovery_can_become_positive_later_exhaustive():
    """thm:philosophy-discovery-can-become-positive-later; Lean: BEDC.GroundCompiler.AnalysisPipeline.StageBridgeObligationDiscovery and BEDC.GroundCompiler.MetricsFlow.MetricCertificateFlow."""
    for initial_net, later_net in product((-0.4, 0.0, 0.8), (-0.4, 0.8)):
        initial = claim(benefit={"coverage": initial_net + 0.2})
        later = claim(benefit={"coverage": later_net + 0.2})
        assert discovery.discovery_becomes_positive_later(initial, later) == (
            discovery.certified_discovery(initial) and discovery.net_information(initial) <= 0.0 and discovery.positive_discovery(later)
        )
    initial = claim(benefit={"coverage": 0.1})
    later = claim(benefit={"coverage": 1.0})
    assert discovery.discovery_becomes_positive_later(initial, later)
    assert not discovery.discovery_becomes_positive_later(later, initial)


def test_philosophy_positive_status_can_decay_exhaustive():
    """thm:philosophy-positive-status-can-decay; Lean: BEDC.GroundCompiler.AnalysisPipeline.LedgerAuditFailureKind.missingLedger and BEDC.GroundCompiler.MetricsFlow.MetricCertificateFlow."""
    before = claim(benefit={"coverage": 1.0})
    for revealed_debt in (0.0, 0.5, 1.0):
        after = claim(benefit={"coverage": 1.0}, omitted={"revealed-critical": revealed_debt} if revealed_debt else {})
        assert discovery.positive_status_decays(before, after) == (discovery.net_information(after) <= 0.0)
    decayed = claim(benefit={"coverage": 1.0}, omitted={"revealed-critical": 1.0})
    stable = claim(benefit={"coverage": 1.0})
    assert discovery.positive_status_decays(before, decayed)
    assert not discovery.positive_status_decays(before, stable)


def test_philosophy_laundering_invalidates_positive_discovery_exhaustive():
    """thm:philosophy-laundering-invalidates-positive-discovery; Lean: BEDC.GroundCompiler.AnalysisPipeline.AnalysisFailureKind.uncertifiedRecognizer and BEDC.GroundCompiler.AnalysisPipeline.LedgerAuditFailureKind.missingLedger."""
    for modes in powerset(("scope", "debt", "classifier")):
        candidate = claim(laundering=frozenset(modes))
        assert discovery.laundering_invalidates(candidate) == bool(modes)
        if modes:
            assert not discovery.positive_discovery(candidate)
    clean = claim()
    laundered = claim(laundering=frozenset({"scope"}))
    assert discovery.positive_discovery(clean)
    assert discovery.laundering_invalidates(laundered)


def test_philosophy_positive_interpretability_discovery_theorem_exhaustive():
    """thm:philosophy-positive-interpretability-discovery-theorem; Lean: BEDC.GroundCompiler.ChapterManuscript.ManuscriptCertificateSound and BEDC.GroundCompiler.ChapterManuscript.ManuscriptLedgerSound."""
    for shifted, rows, public, sealed, omitted, laundering in product(
        (False, True), powerset((SHIFT_ROW,)), (False, True), (False, True), (False, True), (False, True)
    ):
        candidate = claim(
            shifted=shifted,
            passage_rows=rows,
            claim_rows=rows,
            public=public,
            scope_sealed=sealed,
            omitted={"critical": 1.0} if omitted else {},
            laundering=frozenset({"debt"}) if laundering else frozenset(),
        )
        expected = (
            discovery.positive_discovery(candidate)
            and discovery.certified_discovery(candidate)
            and classifier_shift(candidate.passage)
            and ledger_complete(candidate.ledger_required_rows, candidate.ledger_recorded_rows)
            and discovery.protocol_complete(candidate)
            and discovery.protocol_scope_complete(candidate)
            and discovery.debt_complete(candidate)
            and discovery.net_information(candidate) > 0.0
        )
        assert discovery.capstone_positive_interpretability_discovery(candidate) == expected
    positive = claim()
    counter = claim(public=False)
    assert discovery.capstone_positive_interpretability_discovery(positive)
    assert not discovery.capstone_positive_interpretability_discovery(counter)
    assert scoped_resolved(scoped_cert())
