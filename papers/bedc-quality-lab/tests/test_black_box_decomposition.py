from dataclasses import dataclass
from itertools import combinations, product

from bedc_quality_lab import discovery
from bedc_quality_lab.classifier_shift import ClassifierPassage, ClassifierState, classifier_shift
from bedc_quality_lab.hardening import HardeningBackend, HardeningProfile, critical_hardening_gap, fully_hardened_classifier
from bedc_quality_lab.ledger import LedgerEntry, LedgerRowKey, critical_gap, ledger_complete, ledger_debt, ledger_gap
from bedc_quality_lab.metrics import classifier_certificate
from bedc_quality_lab.scope import Scope, ScopedCertificate, scope_rows, scoped_resolved, verification_rows


SOURCE_ROW = LedgerRowKey("source", "behavior-domain")
PATTERN_ROW = LedgerRowKey("pattern", "feature-circuit")
CLASSIFIER_ROW = LedgerRowKey("classifier", "supporting-classifier")
STABILITY_ROW = LedgerRowKey("stability", "declared-scope")
LEDGER_ROW = LedgerRowKey("ledger", "policy")
FEATURE_ROW = LedgerRowKey("pattern", "feature-label")
CIRCUIT_ROW = LedgerRowKey("pattern", "circuit-diagram")
PROBE_ROW = LedgerRowKey("classifier", "probe")
BENCHMARK_ROW = LedgerRowKey("metric", "benchmark-gain")
VERIFY_ROW = LedgerRowKey("verification", "M:B:checked-statement")
TRANSCRIPTION_ROW = LedgerRowKey("verification", "M:B:translation-assumptions")
SHIFT_ROW = LedgerRowKey("classifier", "x->y")
NAMECERT_ROWS = frozenset({SOURCE_ROW, PATTERN_ROW, CLASSIFIER_ROW, STABILITY_ROW, LEDGER_ROW})
CERTIFIED = classifier_certificate({"linear_identifiability_r2": 0.95, "approx_identifiability_proxy": 0.90})
UNCERTIFIED = classifier_certificate({"linear_identifiability_r2": 0.10, "approx_identifiability_proxy": 0.10})
KERNEL_CHECKED = {**CERTIFIED, "verification_status": "kernel-checked"}
SOURCE_IDS = frozenset({"x", "y"})
BASE_RELATION = frozenset({("x", "x", "same"), ("x", "y", "near"), ("y", "y", "same")})
SHIFTED_RELATION = frozenset({("x", "x", "same"), ("x", "y", "far"), ("y", "y", "same")})
SURFACE_PAIR = ("x", "y")


@dataclass(frozen=True)
class BehaviorCase:
    behavior_id: str = "B"
    supports: bool = True
    certificate: dict[str, object] = None
    required_rows: frozenset[LedgerRowKey] = NAMECERT_ROWS
    recorded_rows: frozenset[LedgerRowKey] = NAMECERT_ROWS
    boundary: frozenset[str] = frozenset({"outside-scope"})
    benefit: float = 1.0
    cost: float = 0.2
    debt_cost: float = 0.0


def powerset(values):
    values = tuple(values)
    for size in range(len(values) + 1):
        for members in combinations(values, size):
            yield frozenset(members)


def case(**kwargs):
    kwargs.setdefault("certificate", CERTIFIED)
    if "recorded_rows" not in kwargs and "required_rows" in kwargs:
        kwargs["recorded_rows"] = kwargs["required_rows"]
    return BehaviorCase(**kwargs)


def lab_scope(behavior_id="B"):
    return Scope(frozenset({"D0"}), "M", "A", behavior_id)


def scoped_certificate(item):
    scope = lab_scope(item.behavior_id)
    return ScopedCertificate(
        scope=scope,
        classifier_id="C",
        namecert_id="N",
        required_rows=scope_rows(scope) | item.required_rows,
        recorded_rows=scope_rows(scope) | item.recorded_rows,
        certificate=item.certificate,
        not_claimed_boundary=item.boundary,
    )


def closed_explanation(item):
    return item.supports and item.certificate["cert_status"] == "certified" and ledger_complete(item.required_rows, item.recorded_rows) and scoped_resolved(scoped_certificate(item))


def black_box_behavior(item):
    return item.supports and not closed_explanation(item)


def decomposition_deficit(item):
    gap = ledger_gap(item.required_rows, item.recorded_rows)
    if item.certificate["cert_status"] != "certified":
        gap = gap | frozenset({CLASSIFIER_ROW})
    if not item.boundary:
        gap = gap | frozenset({LedgerRowKey("not-claimed", "boundary")})
    return tuple(1 if row in gap else 0 for row in (SOURCE_ROW, PATTERN_ROW, CLASSIFIER_ROW, STABILITY_ROW, LEDGER_ROW))


def decomposition_debt(item):
    costs = {row: 3.0 if row.kind == "ledger" else 1.0 for row in item.required_rows}
    return ledger_debt(ledger_gap(item.required_rows, item.recorded_rows), costs)


def decomposition_information(item):
    return item.benefit - item.cost - item.debt_cost


def classifier_state(*, shifted=False, certificate=CERTIFIED):
    return ClassifierState(
        source_ids=SOURCE_IDS,
        pattern_id="black-box-decomposition",
        ledger_policy=frozenset({SHIFT_ROW}),
        relation=SHIFTED_RELATION if shifted else BASE_RELATION,
        certificate=certificate,
        surface_used=frozenset({SURFACE_PAIR}),
    )


def passage(*, shifted=True, certificate=CERTIFIED, recorded_rows=frozenset({SHIFT_ROW})):
    return ClassifierPassage(classifier_state(), classifier_state(shifted=shifted, certificate=certificate), recorded_rows)


def hardening_profile(*, recorded=frozenset({VERIFY_ROW, TRANSCRIPTION_ROW}), hardened=frozenset({VERIFY_ROW, TRANSCRIPTION_ROW}), frontier=frozenset(), certificate=CERTIFIED):
    rows = frozenset({VERIFY_ROW, TRANSCRIPTION_ROW})
    return HardeningProfile(certificate, rows, rows, frozenset(), rows, recorded, rows, hardened, frontier, frozenset())


def discovery_claim(*, shifted=True, certificate=CERTIFIED, passage_rows=frozenset({SHIFT_ROW}), claim_rows=frozenset({SHIFT_ROW}), benefit=None, score=None, debt=None, scope_sealed=True, boundary=frozenset({"outside-scope"}), black_box_debt_reduction=1.0, black_box_score_cost=0.2, ndna_complete=False, ndna_anchored=False, ndna_namecert_compatible=False, ndna_ledger_complete=False, ndna_net=0.0):
    cert = scoped_certificate(case(certificate=certificate, boundary=boundary))
    return discovery.DiscoveryClaim(
        passage=passage(shifted=shifted, certificate=certificate, recorded_rows=passage_rows),
        benefit_terms={"coverage": 1.0} if benefit is None else benefit,
        score_terms={"classifier": 0.1} if score is None else score,
        debt_terms={"ledger": 0.1} if debt is None else debt,
        ledger_required_rows=frozenset({SHIFT_ROW}),
        ledger_recorded_rows=claim_rows,
        public_cost_protocol=True,
        scope_sealed=scope_sealed,
        not_claimed_boundary=boundary,
        benefit_modes=frozenset({"coverage"}),
        scoped_certificate=cert,
        black_box_debt_reduction=black_box_debt_reduction,
        black_box_score_cost=black_box_score_cost,
        ndna_complete=ndna_complete,
        ndna_anchored=ndna_anchored,
        ndna_namecert_compatible=ndna_namecert_compatible,
        ndna_ledger_complete=ndna_ledger_complete,
        ndna_net_information=ndna_net,
    )


def test_unexplained_black_box_states_distinct_exhaustive():
    """thm:philosophy-unexplained-black-box-states-distinct; Lean: BEDC.FKernel.NameCert.NameCert; primitive: classifier_certificate, ledger_gap, scoped_resolved."""
    for certificate, rows in product((UNCERTIFIED, CERTIFIED), powerset(NAMECERT_ROWS)):
        assert not black_box_behavior(case(supports=False, certificate=certificate, recorded_rows=rows))
    assert not black_box_behavior(case(supports=False, recorded_rows=frozenset()))
    assert black_box_behavior(case(supports=True, recorded_rows=frozenset()))


def test_partial_certificate_retains_black_box_residue_exhaustive():
    """thm:philosophy-partial-certificate-retains-black-box-residue; Lean: BEDC.Meta.DiscoveryCertificate.NameCertFiveRows; primitive: ledger_gap, ledger_complete."""
    partials = 0
    for rows in powerset(NAMECERT_ROWS):
        missing = ledger_gap(NAMECERT_ROWS, rows)
        if rows and missing:
            partials += 1
            assert black_box_behavior(case(recorded_rows=rows))
            assert not ledger_complete(NAMECERT_ROWS, rows)
    assert partials > 0
    assert black_box_behavior(case(recorded_rows=frozenset({SOURCE_ROW, PATTERN_ROW})))
    assert closed_explanation(case(recorded_rows=NAMECERT_ROWS))


def test_ledger_deficit_blocks_decomposition_closure_exhaustive():
    """thm:philosophy-ledger-deficit-blocks-decomposition-closure; Lean: BEDC.Meta.DiscoveryCertificate.nameCertFiveRows_ledger; primitive: ledger_gap, ledger_complete, critical_gap."""
    for rows in powerset(NAMECERT_ROWS):
        gap = ledger_gap(NAMECERT_ROWS, rows)
        adapters = tuple(LedgerEntry(row, "decomposition", critical=(row == LEDGER_ROW)) for row in gap)
        if LEDGER_ROW not in rows or critical_gap(adapters):
            assert not closed_explanation(case(recorded_rows=rows))
    assert not closed_explanation(case(recorded_rows=NAMECERT_ROWS - {LEDGER_ROW}))
    assert closed_explanation(case(recorded_rows=NAMECERT_ROWS))


def test_closed_explanation_removes_scoped_black_box_status_exhaustive():
    """thm:philosophy-closed-explanation-removes-scoped-black-box-status; Lean: BEDC.Meta.DiscoveryCertificate.after_state_semantic_namecert; primitive: scoped_resolved, ledger_complete."""
    for certificate, rows, boundary in product((UNCERTIFIED, CERTIFIED), powerset(NAMECERT_ROWS), (frozenset(), frozenset({"outside"}))):
        item = case(certificate=certificate, recorded_rows=rows, boundary=boundary)
        if closed_explanation(item):
            assert scoped_resolved(scoped_certificate(item)) and not black_box_behavior(item)
    assert closed_explanation(case())
    assert black_box_behavior(case(boundary=frozenset()))


def test_zero_deficit_field_ledger_closure_exhaustive():
    """thm:philosophy-zero-deficit-field-ledger-closure; Lean: BEDC.FKernel.NameCert.semanticNameCert_ledger_policy_witness; primitive: ledger_gap, ledger_debt."""
    for rows in powerset(NAMECERT_ROWS):
        item = case(recorded_rows=rows)
        gap = ledger_gap(NAMECERT_ROWS, rows)
        assert (decomposition_deficit(item) == (0, 0, 0, 0, 0)) == (not gap)
        assert (decomposition_debt(item) == 0.0) == (not gap)
    assert decomposition_deficit(case()) == (0, 0, 0, 0, 0)
    assert decomposition_deficit(case(recorded_rows=NAMECERT_ROWS - {LEDGER_ROW})) != (0, 0, 0, 0, 0)


def test_decomposition_improvement_reduces_deficit_exhaustive():
    """thm:philosophy-decomposition-improvement-reduces-deficit; Lean: BEDC.Meta.DiscoveryCertificate.discovery_debt_witness; primitive: ledger_debt."""
    improvements = 0
    for before, after in product(powerset(NAMECERT_ROWS), repeat=2):
        before_debt = decomposition_debt(case(recorded_rows=before))
        after_debt = decomposition_debt(case(recorded_rows=after))
        if after_debt < before_debt:
            improvements += 1
            assert ledger_gap(NAMECERT_ROWS, after) != ledger_gap(NAMECERT_ROWS, before)
    assert improvements > 0
    assert decomposition_debt(case(recorded_rows=frozenset({SOURCE_ROW, PATTERN_ROW}))) < decomposition_debt(case(recorded_rows=frozenset({SOURCE_ROW})))


def test_frontier_gives_decomposition_route_exhaustive():
    """thm:philosophy-frontier-gives-decomposition-route; Lean: BEDC.GroundCompiler.ChapterFlow.LedgerSound; primitive: ledger_gap."""
    ledger_required = frozenset({LEDGER_ROW, LedgerRowKey("ledger", "critical-residue")})
    for present, recorded in product(powerset(NAMECERT_ROWS), powerset(ledger_required)):
        frontier = (NAMECERT_ROWS - present) | ledger_gap(ledger_required, recorded)
        assert bool(frontier) == (present != NAMECERT_ROWS or recorded != ledger_required)
    assert (NAMECERT_ROWS - (NAMECERT_ROWS - {STABILITY_ROW})) | ledger_gap(ledger_required, frozenset({LEDGER_ROW}))
    assert not ((NAMECERT_ROWS - NAMECERT_ROWS) | ledger_gap(ledger_required, ledger_required))


def test_ndna_complete_decomposition_yields_bedc_closure_exhaustive():
    """thm:philosophy-ndna-complete-decomposition-yields-bedc-closure; Lean: BEDC.Meta.TheoremDNA.TheoremDNA; primitive: positive_black_box_resolution, scoped_resolved."""
    for complete, anchored, compatible, ledgered, sealed in product((False, True), repeat=5):
        claim = discovery_claim(scope_sealed=sealed, ndna_complete=complete, ndna_anchored=anchored, ndna_namecert_compatible=compatible, ndna_ledger_complete=ledgered, ndna_net=1.0)
        if complete and anchored and compatible and ledgered and sealed:
            assert scoped_resolved(claim.scoped_certificate)
            assert discovery.positive_black_box_resolution(claim)
    assert discovery.positive_black_box_resolution(discovery_claim(ndna_complete=True, ndna_anchored=True, ndna_namecert_compatible=True, ndna_ledger_complete=True, ndna_net=1.0))
    assert not discovery_claim(ndna_complete=True, ndna_anchored=False, ndna_namecert_compatible=True, ndna_ledger_complete=True).ndna_anchored


def test_closure_hardening_separate_axes_exhaustive():
    """thm:philosophy-closure-hardening-separate-axes; Lean: BEDC.GroundCompiler.SelfHostingCompilerFlow.GlobalVerificationSoundness; primitive: scoped_resolved, fully_hardened_classifier."""
    backend = HardeningBackend("lean", frozenset({VERIFY_ROW, TRANSCRIPTION_ROW}))
    for resolved, recorded in product((False, True), powerset((VERIFY_ROW, TRANSCRIPTION_ROW))):
        cert = scoped_certificate(case(recorded_rows=NAMECERT_ROWS if resolved else NAMECERT_ROWS - {LEDGER_ROW}))
        assert scoped_resolved(cert) == resolved
        assert fully_hardened_classifier(hardening_profile(recorded=recorded, hardened=frozenset()), backend) == ledger_complete(backend.hardenable_rows, recorded)
    assert scoped_resolved(scoped_certificate(case())) and not fully_hardened_classifier(hardening_profile(recorded=frozenset(), hardened=frozenset()), backend)
    assert not scoped_resolved(scoped_certificate(case(recorded_rows=NAMECERT_ROWS - {LEDGER_ROW}))) and fully_hardened_classifier(hardening_profile(), backend)


def test_verification_gaps_block_fully_hardened_decomposition_exhaustive():
    """thm:philosophy-verification-gaps-block-fully-hardened-decomposition; Lean: BEDC.GroundCompiler.AnalysisPipeline.CertificateObligationDischarge; primitive: critical_hardening_gap, fully_hardened_classifier."""
    rows = frozenset({VERIFY_ROW, TRANSCRIPTION_ROW})
    backend = HardeningBackend("lean", rows)
    for recorded, hardened, frontier in product(powerset(rows), powerset(rows), powerset(rows)):
        profile = hardening_profile(recorded=recorded, hardened=hardened, frontier=frontier)
        assert critical_hardening_gap(profile, backend) == rows - (recorded | hardened | frontier)
        if critical_hardening_gap(profile, backend) or not ledger_complete(rows, recorded):
            assert not fully_hardened_classifier(profile, backend)
    assert fully_hardened_classifier(hardening_profile(), backend)
    assert not fully_hardened_classifier(hardening_profile(recorded=frozenset({VERIFY_ROW}), hardened=frozenset({VERIFY_ROW})), backend)


def test_closure_does_not_imply_positive_value_exhaustive():
    """thm:philosophy-closure-does-not-imply-positive-value; Lean: BEDC.GroundCompiler.MetricsFlow.MetricCertificateFlow; primitive: positive_black_box_resolution, scoped_resolved."""
    for benefit, cost, debt in product((0.0, 0.5, 1.0), (0.2, 0.8), (0.0, 0.4)):
        item = case(benefit=benefit, cost=cost, debt_cost=debt)
        if closed_explanation(item):
            assert decomposition_information(item) == benefit - cost - debt
    assert closed_explanation(case(benefit=0.1, cost=0.2)) and decomposition_information(case(benefit=0.1, cost=0.2)) <= 0.0
    assert decomposition_information(case(benefit=1.0, cost=0.2)) > 0.0


def test_positive_decomposition_not_automatically_discovery_exhaustive():
    """thm:philosophy-positive-decomposition-not-automatically-discovery; Lean: BEDC.Meta.DiscoveryCertificate.DiscoveryTransition; primitive: positive_information, classifier_shift, positive_discovery."""
    for shifted, benefit, score in product((False, True), (0.0, 1.0), (0.1, 1.2)):
        claim = discovery_claim(shifted=shifted, benefit={"coverage": benefit}, score={"classifier": score})
        if discovery.positive_information(claim) and not classifier_shift(claim.passage):
            assert not discovery.positive_discovery(claim)
    assert discovery.positive_information(discovery_claim(shifted=False, benefit={"ledger": 1.0})) and not discovery.positive_discovery(discovery_claim(shifted=False, benefit={"ledger": 1.0}))
    assert discovery.positive_discovery(discovery_claim(shifted=True, benefit={"coverage": 1.0}))


def test_discovery_resolution_requires_three_conditions_exhaustive():
    """thm:philosophy-discovery-resolution-requires-three-conditions; Lean: BEDC.Meta.DiscoveryCertificate.discovery_transition_witness; primitive: positive_discovery_resolution, positive_discovery, positive_black_box_resolution."""
    for shifted, benefit, reduction in product((False, True), (0.0, 1.0), (0.0, 1.0)):
        claim = discovery_claim(shifted=shifted, benefit={"coverage": benefit}, black_box_debt_reduction=reduction, black_box_score_cost=0.2)
        assert discovery.positive_discovery_resolution(claim) == (discovery.positive_discovery(claim) and discovery.positive_black_box_resolution(claim))
        if discovery.positive_discovery_resolution(claim):
            assert classifier_shift(claim.passage) and discovery.positive_information(claim) and discovery.protocol_scope_complete(claim)
    assert discovery.positive_discovery_resolution(discovery_claim(shifted=True, benefit={"coverage": 1.0}, black_box_debt_reduction=1.0))
    assert not discovery.positive_discovery_resolution(discovery_claim(shifted=False, benefit={"coverage": 1.0}, black_box_debt_reduction=1.0))


def test_feature_circuit_records_not_decompositions_exhaustive():
    """thm:philosophy-feature-circuit-records-not-decompositions; Lean: BEDC.GroundCompiler.SemanticMotif.MotifLedger; primitive: ledger_gap, scoped_resolved."""
    for fragments, pattern in product(powerset((FEATURE_ROW, CIRCUIT_ROW)), powerset((PATTERN_ROW,))):
        item = case(recorded_rows=fragments | pattern)
        assert ledger_gap(NAMECERT_ROWS, item.recorded_rows)
        assert not scoped_resolved(scoped_certificate(item))
        assert black_box_behavior(item)
    assert black_box_behavior(case(recorded_rows=frozenset({FEATURE_ROW, CIRCUIT_ROW})))
    assert closed_explanation(case(recorded_rows=NAMECERT_ROWS))


def test_probe_benchmark_gains_not_decompositions_exhaustive():
    """thm:philosophy-probe-benchmark-gains-not-decompositions; Lean: BEDC.GroundCompiler.MetricsFlow.MetricCertificateFlow; primitive: classifier_certificate, ledger_gap."""
    for r2, proxy, evidence in product((0.7, 0.9), (0.6, 0.8), powerset((PROBE_ROW, BENCHMARK_ROW))):
        cert = classifier_certificate({"linear_identifiability_r2": r2, "approx_identifiability_proxy": proxy})
        item = case(certificate=cert, recorded_rows=evidence)
        assert ledger_gap(NAMECERT_ROWS, evidence)
        assert not closed_explanation(item)
    assert black_box_behavior(case(certificate=CERTIFIED, recorded_rows=frozenset({PROBE_ROW, BENCHMARK_ROW})))
    assert closed_explanation(case(certificate=CERTIFIED, recorded_rows=NAMECERT_ROWS))


def test_local_proof_not_black_box_resolution_exhaustive():
    """thm:philosophy-local-proof-not-black-box-resolution; Lean: BEDC.GroundCompiler.SelfHostingCompilerFlow.GlobalVerificationSoundness; primitive: verification_rows, scoped_resolved, fully_hardened_classifier."""
    proof_cert = scoped_certificate(case(certificate=KERNEL_CHECKED, recorded_rows=frozenset({VERIFY_ROW})))
    backend = HardeningBackend("lean", frozenset({VERIFY_ROW, TRANSCRIPTION_ROW}))
    assert verification_rows(proof_cert)
    for recorded, hardened in product(powerset((VERIFY_ROW, TRANSCRIPTION_ROW)), repeat=2):
        profile = hardening_profile(recorded=recorded, hardened=hardened)
        assert fully_hardened_classifier(profile, backend) == ledger_complete(backend.hardenable_rows, recorded)
        assert not scoped_resolved(proof_cert)
    assert black_box_behavior(case(certificate=KERNEL_CHECKED, recorded_rows=frozenset({VERIFY_ROW})))
    assert closed_explanation(case(certificate=KERNEL_CHECKED, recorded_rows=NAMECERT_ROWS))


def test_bedc_decomposition_machine_learning_black_boxes_exhaustive():
    """thm:philosophy-bedc-decomposition-machine-learning-black-boxes; Lean: BEDC.Meta.DiscoveryCertificate.NameCertFiveRows and BEDC.Meta.TheoremDNA.TheoremDNA; primitive: classifier_certificate, ledger_gap, scoped_resolved, positive_discovery_resolution."""
    states = set()
    for supports, certificate, rows, shifted, reduction in product((False, True), (UNCERTIFIED, CERTIFIED), powerset(NAMECERT_ROWS), (False, True), (0.0, 1.0)):
        item = case(supports=supports, certificate=certificate, recorded_rows=rows)
        claim = discovery_claim(shifted=shifted, certificate=certificate, black_box_debt_reduction=reduction)
        unexplained, residue, resolved = (not supports), black_box_behavior(item), closed_explanation(item)
        resolution = discovery.positive_discovery_resolution(claim)
        assert sum((unexplained, residue, resolved)) == 1
        if resolved:
            assert scoped_resolved(scoped_certificate(item))
        if resolution:
            assert classifier_shift(claim.passage) and discovery.positive_information(claim)
        states.add((unexplained, residue, resolved, resolution))
    assert not black_box_behavior(case(supports=False))
    assert black_box_behavior(case(recorded_rows=NAMECERT_ROWS - {LEDGER_ROW}))
    assert closed_explanation(case())
    assert discovery.positive_discovery_resolution(discovery_claim(shifted=True, black_box_debt_reduction=1.0))
    assert any(state[0] for state in states) and any(state[1] for state in states) and any(state[2] for state in states)
