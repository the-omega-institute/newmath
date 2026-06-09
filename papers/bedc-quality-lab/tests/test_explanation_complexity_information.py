from dataclasses import dataclass, field
from itertools import combinations, product
from typing import Mapping

from bedc_quality_lab.classifier_shift import (
    ClassifierPassage,
    ClassifierState,
    classifier_shift,
    shift_information,
    structural_discovery,
)
from bedc_quality_lab.discovery import (
    DiscoveryClaim,
    capstone_positive_interpretability_discovery,
    critical_debt_free,
    net_information,
    positive_black_box_resolution,
    positive_discovery,
    positive_discovery_resolution,
    positive_information,
    protocol_complete,
)
from bedc_quality_lab.hardening import HardeningBackend, HardeningProfile, critical_hardening_gap, fully_hardened_classifier
from bedc_quality_lab.ledger import LedgerEntry, LedgerRowKey, critical_gap, ledger_complete, ledger_debt, ledger_gap
from bedc_quality_lab.metrics import classifier_certificate
from bedc_quality_lab.scope import Scope, ScopedCertificate, scope_rows, scoped_resolved

SOURCE_IDS = frozenset({"a", "b"})
PAIR = ("a", "b")
SHIFT_ROW = LedgerRowKey("classifier", "a->b")
LEDGER_ROW = LedgerRowKey("ledger", "boundary")
CRITICAL_ROW = LedgerRowKey("verification", "critical")
VERIFY_ROW = LedgerRowKey("verification", "kernel")
SEMANTIC_ROW = LedgerRowKey("semantic", "label")
POLICY = frozenset({SHIFT_ROW})
BASE_RELATION = frozenset({("a", "a", "same"), ("a", "b", "near"), ("b", "b", "same")})
SHIFTED_RELATION = frozenset({("a", "a", "same"), ("a", "b", "far"), ("b", "b", "same")})
CERTIFIED = classifier_certificate({"linear_identifiability_r2": 0.95, "approx_identifiability_proxy": 0.90})
UNCERTIFIED = classifier_certificate({"linear_identifiability_r2": 0.10, "approx_identifiability_proxy": 0.10})


@dataclass(frozen=True)
class ExplanationCase:
    shifted: bool = True
    certificate: Mapping[str, object] = field(default_factory=lambda: CERTIFIED)
    passage_rows: frozenset[LedgerRowKey] = POLICY
    claim_rows: frozenset[LedgerRowKey] = POLICY
    required_rows: frozenset[LedgerRowKey] = POLICY
    benefit_terms: Mapping[str, float] = field(default_factory=lambda: {"coverage": 1.0})
    score_terms: Mapping[str, float] = field(default_factory=lambda: {"classifier": 0.1})
    debt_terms: Mapping[str, float] = field(default_factory=lambda: {"ledger": 0.1})
    public_cost_protocol: bool = True
    weight_profile_public: bool = True
    boundary: frozenset[str] = frozenset({"outside-scope"})
    scope_sealed: bool = True
    critical_debt_rows: frozenset[LedgerRowKey] = frozenset()
    black_box_debt_reduction: float = 0.0
    black_box_score_cost: float = 0.0
    verification_assisted: bool = False
    verification_benefit: float = 0.0
    hardening_profile: HardeningProfile | None = None
    hardening_backend: HardeningBackend | None = None


def powerset(values):
    values = tuple(values)
    for size in range(len(values) + 1):
        for members in combinations(values, size):
            yield frozenset(members)


def score(components, weights) -> float:
    return float(sum(component * weight for component, weight in zip(components, weights)))


def pareto_dominates(left, right) -> bool:
    return all(a >= b for a, b in zip(left, right)) and any(a > b for a, b in zip(left, right))


def selection(benefit: float, score_value: float, debt: float, novelty: bool = False) -> float:
    return benefit + (0.5 if novelty else 0.0) - score_value - debt


def state(*, shifted=True, certificate=CERTIFIED, feature_count=0, record_count=0):
    return ClassifierState(
        SOURCE_IDS,
        "explanation-complexity-information",
        POLICY,
        SHIFTED_RELATION if shifted else BASE_RELATION,
        certificate,
        frozenset({PAIR}),
        feature_count=feature_count,
        record_count=record_count,
    )


def passage(case: ExplanationCase) -> ClassifierPassage:
    return ClassifierPassage(
        state(shifted=False),
        state(shifted=case.shifted, certificate=case.certificate),
        case.passage_rows,
    )


def scoped_cert(
    *,
    certificate=CERTIFIED,
    required_rows=POLICY,
    recorded_rows=POLICY,
    boundary=frozenset({"outside-scope"}),
) -> ScopedCertificate:
    scope = Scope(frozenset({"trace"}), "model", "family", "behavior")
    return ScopedCertificate(
        scope, "classifier", "namecert", scope_rows(scope) | required_rows, scope_rows(scope) | recorded_rows, certificate, boundary
    )


def claim(case: ExplanationCase = ExplanationCase()) -> DiscoveryClaim:
    return DiscoveryClaim(
        passage(case),
        case.benefit_terms,
        case.score_terms,
        case.debt_terms,
        case.required_rows,
        case.claim_rows,
        case.public_cost_protocol,
        case.scope_sealed,
        case.boundary,
        weight_profile_public=case.weight_profile_public,
        scoped_certificate=scoped_cert(
            certificate=case.certificate,
            required_rows=case.required_rows,
            recorded_rows=case.claim_rows,
            boundary=case.boundary,
        ),
        critical_debt_rows=case.critical_debt_rows,
        black_box_debt_reduction=case.black_box_debt_reduction,
        black_box_score_cost=case.black_box_score_cost,
        verification_assisted=case.verification_assisted,
        verification_benefit=case.verification_benefit,
        verification_required_rows=frozenset({VERIFY_ROW}) if case.verification_assisted else frozenset(),
        verification_recorded_rows=frozenset({VERIFY_ROW}) if case.verification_assisted else frozenset(),
        hardening_profile=case.hardening_profile,
        hardening_backend=case.hardening_backend,
    )


def hardening_profile(*, hardened_rows=frozenset(), recorded_rows=frozenset(), critical_rows=frozenset({CRITICAL_ROW})):
    return HardeningProfile(
        CERTIFIED,
        frozenset(),
        frozenset(),
        frozenset(),
        critical_rows,
        recorded_rows,
        critical_rows,
        hardened_rows,
        frozenset(),
        frozenset(),
    )


def test_philosophy_explanation_score_monotone_exhaustive():
    """thm:philosophy-explanation-score-monotone; Lean: BEDC.GroundCompiler.MetricsFlow.MetricCertificateFlow; primitive: classifier_certificate."""
    values = (0.0, 1.0, 2.0)
    weights = (0.0, 0.5, 1.0)
    for left, increments, w in product(product(values, repeat=3), product(values, repeat=3), product(weights, repeat=3)):
        right = tuple(a + b for a, b in zip(left, increments))
        assert score(left, w) <= score(right, w)
    good = classifier_certificate({"linear_identifiability_r2": 0.95, "approx_identifiability_proxy": 0.90})
    weak = classifier_certificate({"linear_identifiability_r2": 0.50, "approx_identifiability_proxy": 0.40})
    assert good["cert_score"] > weak["cert_score"]
    assert score((2.0, 0.0), (0.0, 1.0)) == score((1.0, 0.0), (0.0, 1.0))


def test_philosophy_explanation_score_requires_public_weights_exhaustive():
    """thm:philosophy-explanation-score-requires-public-weights; Lean: BEDC.GroundCompiler.ImplementationInterface.CertificateRecognizerModules; primitive: protocol_complete."""
    left = (1.0, 4.0)
    right = (4.0, 1.0)
    for public in (False, True):
        candidate = claim(ExplanationCase(public_cost_protocol=public, weight_profile_public=public))
        assert protocol_complete(candidate) == public
    assert score(left, (1.0, 0.0)) < score(right, (1.0, 0.0))
    assert score(left, (0.0, 1.0)) > score(right, (0.0, 1.0))
    assert not protocol_complete(claim(ExplanationCase(weight_profile_public=False)))


def test_philosophy_closed_explanation_zero_critical_debt_exhaustive():
    """thm:philosophy-closed-explanation-zero-critical-debt; Lean: BEDC.Meta.DiscoveryCertificate.NameCertFiveRows; primitive: ledger_gap, ledger_debt, critical_gap, scoped_resolved."""
    entries = (
        LedgerEntry(CRITICAL_ROW, "verification", weight=2.0, critical=True),
        LedgerEntry(LEDGER_ROW, "ledger", weight=1.0, critical=False),
    )
    required = frozenset(entry.row for entry in entries)
    costs = {CRITICAL_ROW: 2.0, LEDGER_ROW: 1.0}
    for recorded in powerset(required):
        gap = ledger_gap(required, recorded)
        gap_entries = tuple(entry for entry in entries if entry.row in gap)
        cert = scoped_cert(required_rows=required, recorded_rows=recorded)
        if scoped_resolved(cert):
            assert ledger_debt(gap, costs) == 0.0
            assert not critical_gap(gap_entries)
    assert scoped_resolved(scoped_cert(required_rows=required, recorded_rows=required))
    assert critical_gap(tuple(entry for entry in entries if entry.row == CRITICAL_ROW))


def test_philosophy_critical_debt_blocks_strong_explanation_claims_exhaustive():
    """cor:philosophy-critical-debt-blocks-strong-explanation-claims; Lean: BEDC.GroundCompiler.AnalysisPipeline.CertificateObligationDischarge; primitive: critical_gap, critical_debt_free, fully_hardened_classifier."""
    backend = HardeningBackend("lean", frozenset({CRITICAL_ROW}))
    for rows in powerset((CRITICAL_ROW,)):
        profile = hardening_profile(hardened_rows=rows, recorded_rows=rows)
        candidate = claim(ExplanationCase(critical_debt_rows=frozenset({CRITICAL_ROW}) - rows, hardening_profile=profile, hardening_backend=backend))
        if not critical_debt_free(candidate):
            assert not fully_hardened_classifier(profile, backend)
    clean = claim(ExplanationCase(hardening_profile=hardening_profile(hardened_rows=frozenset({CRITICAL_ROW}), recorded_rows=frozenset({CRITICAL_ROW})), hardening_backend=backend))
    blocked = claim(ExplanationCase(critical_debt_rows=frozenset({CRITICAL_ROW})))
    assert critical_debt_free(clean)
    assert not critical_debt_free(blocked)


def test_philosophy_lower_score_not_positive_net_information_exhaustive():
    """thm:philosophy-lower-score-not-positive-net-information; Lean: BEDC.GroundCompiler.MetricsFlow.QualityMetricEnvelope; primitive: net_information, positive_information."""
    before = claim(ExplanationCase(benefit_terms={"coverage": 1.0}, score_terms={"score": 0.6}, debt_terms={"debt": 0.1}))
    for benefit, after_score, debt in product((0.0, 0.2, 0.4), (0.0, 0.2, 0.4), (0.2, 0.6, 1.0)):
        after = claim(ExplanationCase(benefit_terms={"coverage": benefit}, score_terms={"score": after_score}, debt_terms={"debt": debt}))
        if after_score < 0.6:
            assert net_information(after) - net_information(before) <= 0.0
    lower_positive = claim(ExplanationCase(benefit_terms={"coverage": 2.0}, score_terms={"score": 0.2}, debt_terms={"debt": 0.0}))
    lower_nonpositive = claim(ExplanationCase(benefit_terms={"coverage": 0.0}, score_terms={"score": 0.2}, debt_terms={"debt": 1.0}))
    assert positive_information(lower_positive)
    assert not positive_information(lower_nonpositive)


def test_philosophy_higher_score_positive_net_information_exhaustive():
    """thm:philosophy-higher-score-positive-net-information; Lean: BEDC.GroundCompiler.MetricsFlow.MetricClaimKind.positiveReuseDepthImpliesReuseCertificate; primitive: net_information, positive_information."""
    before = claim(ExplanationCase(benefit_terms={"coverage": 0.4}, score_terms={"score": 0.1}, debt_terms={"debt": 1.0}))
    for benefit, after_score, debt in product((0.6, 1.5, 2.5), (0.2, 0.6), (0.0, 0.5)):
        after = claim(ExplanationCase(benefit_terms={"coverage": benefit}, score_terms={"score": after_score}, debt_terms={"debt": debt}))
        if after_score > 0.1 and net_information(after) > net_information(before):
            assert net_information(after) - net_information(before) > 0.0
    high_positive = claim(ExplanationCase(benefit_terms={"coverage": 2.5}, score_terms={"score": 0.6}, debt_terms={"debt": 0.0}))
    high_negative = claim(ExplanationCase(benefit_terms={"coverage": 0.2}, score_terms={"score": 0.6}, debt_terms={"debt": 0.5}))
    assert positive_information(high_positive)
    assert not positive_information(high_negative)


def test_philosophy_explanation_improvement_need_not_discovery_exhaustive():
    """thm:philosophy-explanation-improvement-need-not-discovery; Lean: BEDC.Meta.ClassifierIncrement.PositiveDiscovery; primitive: positive_information, classifier_shift, positive_discovery."""
    for benefit, rows in product((0.4, 1.0, 2.0), powerset((SHIFT_ROW,))):
        candidate = claim(ExplanationCase(shifted=False, benefit_terms={"ledger": benefit}, passage_rows=rows, claim_rows=rows))
        if positive_information(candidate):
            assert not classifier_shift(candidate.passage)
            assert not positive_discovery(candidate)
    improvement = claim(ExplanationCase(shifted=False, benefit_terms={"ledger": 2.0}))
    discovery_case = claim(ExplanationCase(benefit_terms={"coverage": 2.0}))
    assert positive_information(improvement) and not positive_discovery(improvement)
    assert positive_discovery(discovery_case)


def test_philosophy_interpretability_discovery_need_not_positive_exhaustive():
    """thm:philosophy-interpretability-discovery-need-not-positive; Lean: BEDC.Meta.DiscoveryCertificate.structuralDiscovery_classifier_shift; primitive: structural_discovery, shift_information, positive_discovery."""
    for benefit, debt in product((0.0, 0.2, 1.0), (0.2, 1.0, 2.0)):
        candidate = claim(ExplanationCase(benefit_terms={"coverage": benefit}, debt_terms={"ledger": debt}))
        if structural_discovery(candidate.passage) and net_information(candidate) <= 0.0:
            assert shift_information(candidate.passage) > 0
            assert not positive_discovery(candidate)
    novelty_only = claim(ExplanationCase(benefit_terms={"coverage": 0.0}, debt_terms={"ledger": 1.0}))
    positive = claim(ExplanationCase(benefit_terms={"coverage": 2.0}))
    assert structural_discovery(novelty_only.passage) and not positive_discovery(novelty_only)
    assert positive_discovery(positive)


def test_philosophy_positive_discovery_two_audits_exhaustive():
    """thm:philosophy-positive-discovery-two-audits; Lean: BEDC.Meta.DiscoveryCertificate.positiveDiscovery_classifier_shift; primitive: positive_discovery, classifier_shift, positive_information."""
    for shifted, benefit in product((False, True), (0.0, 0.4, 2.0)):
        candidate = claim(ExplanationCase(shifted=shifted, benefit_terms={"coverage": benefit}))
        if positive_discovery(candidate):
            assert classifier_shift(candidate.passage)
            assert positive_information(candidate)
    positive = claim(ExplanationCase(benefit_terms={"coverage": 2.0}))
    no_novelty = claim(ExplanationCase(shifted=False, benefit_terms={"coverage": 2.0}))
    assert positive_discovery(positive)
    assert positive_information(no_novelty) and not positive_discovery(no_novelty)


def test_philosophy_counts_do_not_determine_interpretability_information_exhaustive():
    """thm:philosophy-counts-do-not-determine-interpretability-information; Lean: BEDC.GroundCompiler.MetricsFlow.QualityMetricEnvelope; primitive: net_information."""
    for counts in product((0, 1, 3), repeat=4):
        low = claim(ExplanationCase(benefit_terms={"coverage": 0.2}, score_terms={"count": 0.2}, debt_terms={"debt": 0.4}))
        high = claim(ExplanationCase(benefit_terms={"coverage": 2.0}, score_terms={"count": 0.2}, debt_terms={"debt": 0.1}))
        assert len(counts) == 4
        assert net_information(high) > net_information(low)
    many_low = claim(ExplanationCase(benefit_terms={"coverage": 0.1}, score_terms={"count": 1.0}, debt_terms={"debt": 1.0}))
    few_high = claim(ExplanationCase(benefit_terms={"coverage": 2.0}, score_terms={"count": 0.1}, debt_terms={"debt": 0.0}))
    aligned = claim(ExplanationCase(benefit_terms={"coverage": 1.0}, score_terms={"count": 0.1}, debt_terms={"debt": 0.1}))
    assert net_information(few_high) > net_information(many_low)
    assert net_information(aligned) > 0.0


def test_philosophy_feature_discovery_requires_certificate_value_exhaustive():
    """cor:philosophy-feature-discovery-requires-certificate-value; Lean: BEDC.GroundCompiler.NameCertGenerated.NameCertClassifierSoundnessEvent; primitive: classifier_certificate, classifier_shift, net_information."""
    for feature_count, certificate, shifted in product((0, 3, 8), (UNCERTIFIED, CERTIFIED), (False, True)):
        candidate = ClassifierPassage(
            source=state(shifted=False, feature_count=0),
            target=state(shifted=shifted, certificate=certificate, feature_count=feature_count),
            recorded_rows=POLICY,
        )
        if feature_count > 0 and (not shifted or certificate["cert_status"] != "certified"):
            assert not structural_discovery(candidate)
    feature_only = claim(ExplanationCase(shifted=False, benefit_terms={"features": 2.0}))
    certified_value = claim(ExplanationCase(benefit_terms={"features": 2.0}))
    assert positive_information(feature_only) and not positive_discovery(feature_only)
    assert positive_discovery(certified_value)


def test_philosophy_proof_quantity_not_explanation_quality_exhaustive():
    """cor:philosophy-proof-quantity-not-explanation-quality; Lean: BEDC.GroundCompiler.SelfHostingCompilerFlow.GlobalVerificationSoundness; primitive: fully_hardened_classifier, net_information."""
    backend = HardeningBackend("lean", frozenset({CRITICAL_ROW}))
    for proof_rows, benefit in product(powerset((CRITICAL_ROW, VERIFY_ROW)), (0.0, 2.0)):
        profile = hardening_profile(hardened_rows=proof_rows, recorded_rows=proof_rows & frozenset({CRITICAL_ROW}))
        candidate = claim(ExplanationCase(benefit_terms={"verification": benefit}, hardening_profile=profile, hardening_backend=backend))
        if fully_hardened_classifier(profile, backend):
            assert CRITICAL_ROW in proof_rows
            assert abs(net_information(candidate) - (benefit - 0.2)) < 1e-12
    many_low = claim(ExplanationCase(benefit_terms={"verification": 0.0}, score_terms={"proofs": 1.0}, debt_terms={"debt": 1.0}))
    one_high_profile = hardening_profile(hardened_rows=frozenset({CRITICAL_ROW}), recorded_rows=frozenset({CRITICAL_ROW}))
    one_high = claim(ExplanationCase(benefit_terms={"verification": 2.0}, hardening_profile=one_high_profile, hardening_backend=backend))
    assert net_information(one_high) > net_information(many_low)
    assert fully_hardened_classifier(one_high_profile, backend)


def test_philosophy_no_hidden_scalar_captures_explanation_quality_exhaustive():
    """thm:philosophy-no-hidden-scalar-captures-explanation-quality; Lean: BEDC.GroundCompiler.ImplementationInterface.CertificateRecognizerModules; primitive: protocol_complete."""
    low_cost_high_debt = (1.0, -0.1, -1.0, 0.0, 0.0)
    high_cost_low_debt = (1.0, -1.0, -0.1, 0.0, 0.0)
    for weights in ((0.0, 1.0, 0.0, 0.0, 0.0), (0.0, 0.0, 1.0, 0.0, 0.0)):
        assert score(low_cost_high_debt, weights) != score(high_cost_low_debt, weights)
    hidden = claim(ExplanationCase(weight_profile_public=False))
    dominated = (2.0, -0.1, -0.1, 1.0, 1.0)
    assert not protocol_complete(hidden)
    assert pareto_dominates(dominated, low_cost_high_debt)


def test_philosophy_explanation_comparison_vectors_or_public_weights_exhaustive():
    """cor:philosophy-explanation-comparison-vectors-or-public-weights; Lean: BEDC.GroundCompiler.ImplementationInterface.CertificateRecognizerModules; primitive: protocol_complete."""
    candidates = ((1.0, -0.1, -1.0, 0.0, 0.0), (1.0, -1.0, -0.1, 0.0, 0.0), (2.0, -0.1, -0.1, 1.0, 1.0))
    for left, right in product(candidates, repeat=2):
        if pareto_dominates(left, right):
            assert left != right
    public = claim()
    opaque = claim(ExplanationCase(weight_profile_public=False))
    assert protocol_complete(public)
    assert not protocol_complete(opaque)
    assert pareto_dominates(candidates[2], candidates[0])


def test_philosophy_shortest_explanation_not_selection_favorable_exhaustive():
    """thm:philosophy-shortest-explanation-not-selection-favorable; Lean: BEDC.Meta.ClassifierIncrement.PositiveDiscovery; primitive: classifier_shift, positive_information."""
    for short_benefit, long_benefit in product((0.0, 0.5), (1.0, 2.0)):
        short_value = selection(short_benefit, score_value=0.1, debt=1.0, novelty=False)
        long_value = selection(long_benefit, score_value=0.6, debt=0.0, novelty=True)
        assert long_value > short_value
    short = claim(ExplanationCase(shifted=False, benefit_terms={"label": 0.1}, score_terms={"score": 0.1}, debt_terms={"debt": 1.0}))
    long = claim(ExplanationCase(benefit_terms={"coverage": 2.0}, score_terms={"score": 0.6}, debt_terms={"debt": 0.0}))
    assert not classifier_shift(short.passage)
    assert classifier_shift(long.passage) and positive_information(long)


def test_philosophy_ledger_heavy_explanations_safety_favorable_exhaustive():
    """thm:philosophy-ledger-heavy-explanations-safety-favorable; Lean: BEDC.GroundCompiler.ChapterFlow.LedgerSound; primitive: ledger_gap, ledger_debt."""
    required = frozenset({LEDGER_ROW, SEMANTIC_ROW})
    costs = {LEDGER_ROW: 2.0, SEMANTIC_ROW: 2.0}
    for before_rows, after_rows in product(powerset(required), repeat=2):
        if before_rows.issubset(after_rows):
            before_debt = ledger_debt(ledger_gap(required, before_rows), costs)
            after_debt = ledger_debt(ledger_gap(required, after_rows), costs)
            before_value = -0.1 * len(before_rows) - before_debt
            after_value = -0.1 * len(after_rows) - after_debt
            assert after_value >= before_value
    sparse = frozenset()
    heavy = required
    assert ledger_complete(required, heavy)
    assert ledger_debt(ledger_gap(required, heavy), costs) < ledger_debt(ledger_gap(required, sparse), costs)


def test_philosophy_debt_reduction_justifies_higher_complexity_exhaustive():
    """thm:philosophy-debt-reduction-justifies-higher-complexity; Lean: BEDC.Meta.DiscoveryCertificate.discovery_debt_witness; primitive: positive_black_box_resolution, net_information."""
    for reduction, cost in product((0.0, 0.4, 1.2), (0.1, 0.5, 1.0)):
        candidate = claim(ExplanationCase(black_box_debt_reduction=reduction, black_box_score_cost=cost))
        assert positive_black_box_resolution(candidate) == (reduction - cost > 0.0)
    before = claim(ExplanationCase(benefit_terms={"coverage": 0.0}, score_terms={"score": 0.1}, debt_terms={"black-box": 1.2}))
    after = claim(ExplanationCase(benefit_terms={"coverage": 0.3}, score_terms={"score": 0.5}, debt_terms={"black-box": 0.0}, black_box_debt_reduction=1.2, black_box_score_cost=0.4))
    counter = claim(ExplanationCase(black_box_debt_reduction=0.2, black_box_score_cost=0.5))
    assert net_information(after) > net_information(before)
    assert positive_black_box_resolution(after)
    assert not positive_black_box_resolution(counter)


def test_philosophy_formal_hardening_net_gain_exhaustive():
    """thm:philosophy-formal-hardening-net-gain; Lean: BEDC.GroundCompiler.SelfHostingCompilerFlow.GlobalVerificationSoundness; primitive: fully_hardened_classifier, critical_hardening_gap, net_information."""
    backend = HardeningBackend("lean", frozenset({CRITICAL_ROW}))
    for hardened_rows, benefit, cost in product(powerset((CRITICAL_ROW,)), (0.0, 0.5, 2.0), (0.1, 1.0)):
        profile = hardening_profile(hardened_rows=hardened_rows, recorded_rows=hardened_rows)
        candidate = claim(ExplanationCase(benefit_terms={"verification": benefit}, score_terms={"verification": cost}, debt_terms={"verification": 0.0}, hardening_profile=profile, hardening_backend=backend))
        if fully_hardened_classifier(profile, backend) and net_information(candidate) > 0.0:
            assert not critical_hardening_gap(profile, backend)
    gain_profile = hardening_profile(hardened_rows=frozenset({CRITICAL_ROW}), recorded_rows=frozenset({CRITICAL_ROW}))
    gain = claim(ExplanationCase(benefit_terms={"verification": 2.0}, score_terms={"verification": 0.2}, debt_terms={"verification": 0.0}, hardening_profile=gain_profile, hardening_backend=backend))
    loss = claim(ExplanationCase(benefit_terms={"verification": 0.0}, score_terms={"verification": 1.0}, debt_terms={"verification": 0.0}, hardening_profile=gain_profile, hardening_backend=backend))
    assert fully_hardened_classifier(gain_profile, backend)
    assert positive_information(gain)
    assert not positive_information(loss)


def test_philosophy_explanation_complexity_information_theorem_exhaustive():
    """thm:philosophy-explanation-complexity-information-theorem; Lean: BEDC.Meta.DiscoveryCertificate.PositiveDiscovery; primitive: capstone_positive_interpretability_discovery, positive_discovery, classifier_shift, net_information."""
    for shifted, benefit, certificate, rows in product((False, True), (0.0, 2.0), (UNCERTIFIED, CERTIFIED), powerset((SHIFT_ROW,))):
        candidate = claim(
            ExplanationCase(
                shifted=shifted,
                certificate=certificate,
                passage_rows=rows,
                claim_rows=rows,
                benefit_terms={"coverage": benefit},
            )
        )
        if capstone_positive_interpretability_discovery(candidate):
            assert positive_discovery(candidate)
            assert classifier_shift(candidate.passage)
            assert net_information(candidate) > 0.0
    positive = claim(ExplanationCase(benefit_terms={"coverage": 2.0}))
    brevity_only = claim(ExplanationCase(shifted=False, benefit_terms={"label": 0.0}, score_terms={"score": 0.0}, debt_terms={"debt": 1.0}))
    resolution = claim(ExplanationCase(benefit_terms={"coverage": 2.0}, black_box_debt_reduction=1.0, black_box_score_cost=0.1))
    assert capstone_positive_interpretability_discovery(positive)
    assert not capstone_positive_interpretability_discovery(brevity_only)
    assert positive_discovery_resolution(resolution)
