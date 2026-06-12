from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations, product

from bedc_quality_lab.classifier_shift import (
    ClassifierPassage,
    ClassifierState,
    classifier_shift,
    structural_discovery,
)
from bedc_quality_lab.discovery import (
    DiscoveryClaim,
    apparent_net_information,
    net_information,
    ndna_positive_criterion,
    positive_discovery,
    positive_discovery_resolution,
    positive_information,
)
from bedc_quality_lab.hardening import (
    HardeningBackend,
    HardeningProfile,
    critical_hardening_gap,
    fully_hardened_classifier,
    local_hardening_delta,
)
from bedc_quality_lab.ledger import LedgerRowKey, ledger_complete, ledger_gap
from bedc_quality_lab.metrics import classifier_certificate
from bedc_quality_lab.scope import Scope, ScopedCertificate, scoped_resolved, scope_rows


CERTIFIED = classifier_certificate({"linear_identifiability_r2": 0.95, "approx_identifiability_proxy": 0.90})
UNCERTIFIED = classifier_certificate({"linear_identifiability_r2": 0.10, "approx_identifiability_proxy": 0.10})

MATERIAL_ROW = LedgerRowKey("material", "traceable-record")
CLASSIFIER_ROW = LedgerRowKey("classifier", "source->target")
NAMECERT_SOURCE_ROW = LedgerRowKey("namecert", "source")
NAMECERT_PATTERN_ROW = LedgerRowKey("namecert", "pattern")
NAMECERT_CLASSIFIER_ROW = LedgerRowKey("namecert", "classifier")
NAMECERT_STABILITY_ROW = LedgerRowKey("namecert", "stability")
NAMECERT_LEDGER_POLICY_ROW = LedgerRowKey("namecert", "ledger-policy")
LEDGER_ROW = LedgerRowKey("ledger", "required-residue")
DNA_COMPLETE_ROW = LedgerRowKey("dna", "complete")
DNA_ANCHORED_ROW = LedgerRowKey("dna", "anchored")
DNA_COMPATIBLE_ROW = LedgerRowKey("dna", "certificate-compatible")
SCOPE_ROUTE_ROW = LedgerRowKey("scope", "closure-route")
VERIFICATION_ROW = LedgerRowKey("verification", "critical-component")
VERIFICATION_LEDGER_ROW = LedgerRowKey("verification-ledger", "critical-component")
NON_HARDENABLE_ROW = LedgerRowKey("verification", "semantic-residue")

NAMECERT_ROWS = frozenset(
    {
        NAMECERT_SOURCE_ROW,
        NAMECERT_PATTERN_ROW,
        NAMECERT_CLASSIFIER_ROW,
        NAMECERT_STABILITY_ROW,
        NAMECERT_LEDGER_POLICY_ROW,
    }
)
DNA_ROWS = frozenset({DNA_COMPLETE_ROW, DNA_ANCHORED_ROW, DNA_COMPATIBLE_ROW})
THEORY_ROWS = frozenset({MATERIAL_ROW, CLASSIFIER_ROW, LEDGER_ROW, SCOPE_ROUTE_ROW}) | NAMECERT_ROWS | DNA_ROWS
ALL_ROWS = THEORY_ROWS | frozenset({VERIFICATION_ROW, VERIFICATION_LEDGER_ROW, NON_HARDENABLE_ROW})

BASE_RELATION = frozenset({("source", "target", "same")})
SHIFTED_RELATION = frozenset({("source", "target", "different")})
SURFACE = frozenset({("source", "target")})


@dataclass(frozen=True)
class UnifiedObjectCase:
    material_traceable: bool = True
    classifier_displayed: bool = True
    namecert_source: bool = True
    namecert_pattern: bool = True
    namecert_classifier: bool = True
    namecert_stability: bool = True
    namecert_ledger_policy: bool = True
    ledgered: bool = True
    dna_complete: bool = True
    dna_anchored: bool = True
    dna_certificate_compatible: bool = True
    scope_sealed: bool = True
    claim_kind_stated: bool = True
    not_claimed_boundary: bool = True
    closure_route_stated: bool = True
    verification_hardened: bool = False
    verification_ledgered: bool = False
    non_hardenable_ledgered: bool = True
    certified: bool = True
    debt: float = 0.0


def powerset(values):
    values = tuple(values)
    for size in range(len(values) + 1):
        for members in combinations(values, size):
            yield frozenset(members)


def case_from_rows(rows: frozenset[LedgerRowKey], **overrides) -> UnifiedObjectCase:
    base = UnifiedObjectCase(
        material_traceable=MATERIAL_ROW in rows,
        classifier_displayed=CLASSIFIER_ROW in rows,
        namecert_source=NAMECERT_SOURCE_ROW in rows,
        namecert_pattern=NAMECERT_PATTERN_ROW in rows,
        namecert_classifier=NAMECERT_CLASSIFIER_ROW in rows,
        namecert_stability=NAMECERT_STABILITY_ROW in rows,
        namecert_ledger_policy=NAMECERT_LEDGER_POLICY_ROW in rows,
        ledgered=LEDGER_ROW in rows,
        dna_complete=DNA_COMPLETE_ROW in rows,
        dna_anchored=DNA_ANCHORED_ROW in rows,
        dna_certificate_compatible=DNA_COMPATIBLE_ROW in rows,
        scope_sealed=SCOPE_ROUTE_ROW in rows,
        claim_kind_stated=SCOPE_ROUTE_ROW in rows,
        not_claimed_boundary=SCOPE_ROUTE_ROW in rows,
        closure_route_stated=SCOPE_ROUTE_ROW in rows,
        verification_hardened=VERIFICATION_ROW in rows,
        verification_ledgered=VERIFICATION_LEDGER_ROW in rows,
        non_hardenable_ledgered=NON_HARDENABLE_ROW in rows,
    )
    return UnifiedObjectCase(**(base.__dict__ | overrides))


def namecert_closed(case: UnifiedObjectCase) -> bool:
    return (
        case.namecert_source
        and case.namecert_pattern
        and case.namecert_classifier
        and case.namecert_stability
        and case.namecert_ledger_policy
        and case.certified
    )


def dna_closed(case: UnifiedObjectCase) -> bool:
    return case.dna_complete and case.dna_anchored and case.dna_certificate_compatible


def scope_closed(case: UnifiedObjectCase) -> bool:
    return case.scope_sealed and case.claim_kind_stated and case.not_claimed_boundary and case.closure_route_stated


def theory_closed(case: UnifiedObjectCase) -> bool:
    return (
        case.material_traceable
        and case.classifier_displayed
        and namecert_closed(case)
        and case.ledgered
        and dna_closed(case)
        and scope_closed(case)
    )


def verification_closed(case: UnifiedObjectCase) -> bool:
    return case.verification_hardened and case.verification_ledgered and case.non_hardenable_ledgered


def fully_hardened_closed(case: UnifiedObjectCase) -> bool:
    return theory_closed(case) and verification_closed(case)


def recorded_rows(case: UnifiedObjectCase) -> frozenset[LedgerRowKey]:
    rows = set()
    if case.material_traceable:
        rows.add(MATERIAL_ROW)
    if case.classifier_displayed:
        rows.add(CLASSIFIER_ROW)
    if case.namecert_source:
        rows.add(NAMECERT_SOURCE_ROW)
    if case.namecert_pattern:
        rows.add(NAMECERT_PATTERN_ROW)
    if case.namecert_classifier:
        rows.add(NAMECERT_CLASSIFIER_ROW)
    if case.namecert_stability:
        rows.add(NAMECERT_STABILITY_ROW)
    if case.namecert_ledger_policy:
        rows.add(NAMECERT_LEDGER_POLICY_ROW)
    if case.ledgered:
        rows.add(LEDGER_ROW)
    if case.dna_complete:
        rows.add(DNA_COMPLETE_ROW)
    if case.dna_anchored:
        rows.add(DNA_ANCHORED_ROW)
    if case.dna_certificate_compatible:
        rows.add(DNA_COMPATIBLE_ROW)
    if scope_closed(case):
        rows.add(SCOPE_ROUTE_ROW)
    if case.verification_ledgered:
        rows.add(VERIFICATION_LEDGER_ROW)
    if case.non_hardenable_ledgered:
        rows.add(NON_HARDENABLE_ROW)
    return frozenset(rows)


def unified_scope() -> Scope:
    return Scope(
        domain_ids=frozenset({"source", "target"}),
        model_id="unified-theory-closure",
        admitted_family_id="classifier-surface",
        behavior_id="closure-route",
    )


def scoped_certificate(case: UnifiedObjectCase) -> ScopedCertificate:
    scope = unified_scope()
    required = scope_rows(scope) | frozenset({SCOPE_ROUTE_ROW})
    recorded = required if scope_closed(case) else frozenset()
    return ScopedCertificate(
        scope=scope,
        classifier_id="unified-classifier",
        namecert_id="unified-namecert",
        required_rows=required,
        recorded_rows=recorded,
        certificate=CERTIFIED if case.certified else UNCERTIFIED,
        not_claimed_boundary=frozenset({"outside-declared-scope"}) if case.not_claimed_boundary else frozenset(),
    )


def hardening_backend() -> HardeningBackend:
    return HardeningBackend(
        backend_id="lean-kernel",
        hardenable_rows=frozenset({VERIFICATION_ROW}),
    )


def hardening_profile(case: UnifiedObjectCase) -> HardeningProfile:
    return HardeningProfile(
        certificate=CERTIFIED if case.certified else UNCERTIFIED,
        mode_rows=frozenset(),
        declared_mode_rows=frozenset(),
        open_mode_rows=frozenset(),
        ledger_required_rows=frozenset({VERIFICATION_LEDGER_ROW, NON_HARDENABLE_ROW}),
        ledger_recorded_rows=recorded_rows(case) & frozenset({VERIFICATION_LEDGER_ROW, NON_HARDENABLE_ROW}),
        critical_rows=frozenset({VERIFICATION_ROW}),
        hardened_rows=frozenset({VERIFICATION_ROW}) if case.verification_hardened else frozenset(),
        frontier_rows=frozenset(),
        non_hardenable_residue=frozenset({NON_HARDENABLE_ROW}),
    )


def classifier_state(*, shifted: bool, certified: bool = True, records: int = 1) -> ClassifierState:
    return ClassifierState(
        source_ids=frozenset({"source", "target"}),
        pattern_id="unified-theory-closure",
        ledger_policy=frozenset({CLASSIFIER_ROW}),
        relation=SHIFTED_RELATION if shifted else BASE_RELATION,
        certificate=CERTIFIED if certified else UNCERTIFIED,
        surface_used=SURFACE,
        verification_status="kernel-checked" if certified else "unverified",
        record_count=records,
    )


def classifier_passage(*, shifted: bool, certified: bool = True, ledgered: bool = True, records: int = 2) -> ClassifierPassage:
    return ClassifierPassage(
        source=classifier_state(shifted=False, records=1),
        target=classifier_state(shifted=shifted, certified=certified, records=records),
        recorded_rows=frozenset({CLASSIFIER_ROW}) if ledgered else frozenset(),
    )


def discovery_claim(
    *,
    shifted: bool = True,
    closed: bool = True,
    benefit: float = 1.0,
    cost: float = 0.1,
    debt: float = 0.1,
    omitted_debt: float = 0.0,
    certified: bool = True,
    scope_sealed: bool = True,
    ledgered: bool = True,
    laundering: bool = False,
    verification_hardened: bool = False,
    verification_ledgered: bool = False,
    non_hardenable_ledgered: bool = True,
    ndna: bool = False,
    black_box: bool = False,
) -> DiscoveryClaim:
    case = UnifiedObjectCase(
        ledgered=closed and ledgered,
        scope_sealed=closed and scope_sealed,
        claim_kind_stated=closed and scope_sealed,
        not_claimed_boundary=closed and scope_sealed,
        closure_route_stated=closed and scope_sealed,
        certified=certified,
        verification_hardened=verification_hardened,
        verification_ledgered=verification_ledgered,
        non_hardenable_ledgered=non_hardenable_ledgered,
        dna_complete=closed,
        dna_anchored=closed,
        dna_certificate_compatible=closed,
    )
    return DiscoveryClaim(
        passage=classifier_passage(shifted=shifted, certified=certified, ledgered=ledgered),
        benefit_terms={"unified": benefit},
        score_terms={"namecert-ledger-dna-verification-seal-maintenance": cost},
        debt_terms={"ledger-semantic-verification-generalization-intervention-dna-scope": debt},
        ledger_required_rows=THEORY_ROWS,
        ledger_recorded_rows=recorded_rows(case),
        public_cost_protocol=True,
        scope_sealed=scope_sealed,
        not_claimed_boundary=frozenset({"outside-declared-scope"}) if scope_sealed else frozenset(),
        scoped_certificate=scoped_certificate(case),
        hardening_profile=hardening_profile(case),
        hardening_backend=hardening_backend(),
        omitted_debt_terms={"hidden": omitted_debt} if omitted_debt else {},
        ndna_complete=ndna and case.dna_complete,
        ndna_anchored=ndna and case.dna_anchored,
        ndna_namecert_compatible=ndna and case.dna_certificate_compatible,
        ndna_ledger_complete=ndna and case.ledgered,
        ndna_net_information=benefit - cost - debt - omitted_debt if ndna else 0.0,
        black_box_debt_reduction=0.5 if black_box else 0.0,
        black_box_score_cost=0.1 if black_box else 0.0,
        laundering_modes=frozenset({"hidden-debt"}) if laundering else frozenset(),
    )


def test_hardening_closure_implies_theory_closure_exhaustive():
    """thm:philosophy-hardening-closure-implies-theory-closure; Lean: BEDC.FKernel.Gap.CompCoverage.hardening_composite_coverage; primitive: fully_hardened_classifier, critical_hardening_gap; fixture: UnifiedObjectCase."""
    backend = hardening_backend()
    for rows in powerset(ALL_ROWS):
        case = case_from_rows(rows)
        profile = hardening_profile(case)
        hardened = fully_hardened_closed(case)
        primitive_hardened = fully_hardened_classifier(profile, backend)
        if hardened:
            assert theory_closed(case)
            assert primitive_hardened
            assert critical_hardening_gap(profile, backend) == frozenset()
        if primitive_hardened and theory_closed(case):
            assert ledger_complete(THEORY_ROWS, recorded_rows(case))
    assert fully_hardened_closed(UnifiedObjectCase(verification_hardened=True, verification_ledgered=True))
    assert not fully_hardened_closed(UnifiedObjectCase(ledgered=False, verification_hardened=True, verification_ledgered=True))


def test_namecert_without_ledger_not_theory_closure_exhaustive():
    """thm:philosophy-namecert-without-ledger-not-theory-closure; Lean: BEDC.GroundCompiler.NameCertGenerated.namecert_without_ledger_not_admissible; primitive: ledger_complete, ledger_gap; fixture: UnifiedObjectCase."""
    for ledgered, namecert_extra in product((False, True), powerset(NAMECERT_ROWS)):
        rows = frozenset({MATERIAL_ROW, CLASSIFIER_ROW, *namecert_extra, *DNA_ROWS, SCOPE_ROUTE_ROW})
        if ledgered:
            rows = rows | frozenset({LEDGER_ROW})
        case = case_from_rows(rows)
        assert namecert_closed(case) == NAMECERT_ROWS.issubset(rows)
        if namecert_closed(case) and not ledgered:
            assert not theory_closed(case)
            assert ledger_gap(THEORY_ROWS, recorded_rows(case)) == frozenset({LEDGER_ROW})
    assert not theory_closed(UnifiedObjectCase(ledgered=False))
    assert theory_closed(UnifiedObjectCase())


def test_dna_without_namecert_not_theory_closure_exhaustive():
    """thm:philosophy-dna-without-namecert-not-theory-closure; Lean: BEDC.FKernel.NameCert.NameCert_iff_semantic_fields; primitive: ledger_complete; fixture: UnifiedObjectCase."""
    for namecert_rows in powerset(NAMECERT_ROWS):
        rows = frozenset({MATERIAL_ROW, CLASSIFIER_ROW, LEDGER_ROW, *DNA_ROWS, SCOPE_ROUTE_ROW, *namecert_rows})
        case = case_from_rows(rows)
        assert dna_closed(case)
        if namecert_rows != NAMECERT_ROWS:
            assert not namecert_closed(case)
            assert not theory_closed(case)
        else:
            assert theory_closed(case)
            assert ledger_complete(THEORY_ROWS, recorded_rows(case))
    assert not theory_closed(UnifiedObjectCase(namecert_classifier=False))


def test_verification_does_not_replace_ledger_closure_exhaustive():
    """thm:philosophy-verification-does-not-replace-ledger-closure; Lean: BEDC.GroundCompiler.ProgrammaticRealization.checker_program_not_certificate_evidence; primitive: fully_hardened_classifier, ledger_complete; fixture: UnifiedObjectCase."""
    backend = hardening_backend()
    for ledgered, verification_hardened, verification_ledgered in product((False, True), repeat=3):
        case = UnifiedObjectCase(
            ledgered=ledgered,
            verification_hardened=verification_hardened,
            verification_ledgered=verification_ledgered,
        )
        if verification_hardened and verification_ledgered and not ledgered:
            assert verification_closed(case)
            assert not theory_closed(case)
            assert not ledger_complete(THEORY_ROWS, recorded_rows(case))
        if fully_hardened_classifier(hardening_profile(case), backend) and ledgered:
            assert verification_closed(case)
    assert not theory_closed(UnifiedObjectCase(ledgered=False, verification_hardened=True, verification_ledgered=True))


def test_positive_uinfo_not_classifier_discovery_exhaustive():
    """thm:philosophy-positive-uinfo-not-classifier-discovery; Lean: BEDC.GroundCompiler.MetricsFlow.metrics_cannot_replace_certificates; primitive: positive_information, classifier_shift; fixture: DiscoveryClaim."""
    for benefit, cost, debt in product((0.0, 0.5, 1.0), (0.1, 0.4), (0.0, 0.2)):
        claim = discovery_claim(shifted=False, benefit=benefit, cost=cost, debt=debt)
        assert positive_information(claim) == (benefit - cost - debt > 0.0)
        assert not classifier_shift(claim.passage)
        assert not positive_discovery(claim)
    assert positive_information(discovery_claim(shifted=False, benefit=1.0, cost=0.1, debt=0.1))


def test_classifier_shift_not_positive_uinfo_exhaustive():
    """thm:philosophy-classifier-shift-not-positive-uinfo; Lean: BEDC.GroundCompiler.MetricsFlow.forbidden_metric_claims_need_certificates; primitive: classifier_shift, net_information, positive_discovery; fixture: DiscoveryClaim."""
    for benefit, cost, debt in product((0.0, 0.2, 1.0), (0.1, 0.6), (0.2, 0.8)):
        claim = discovery_claim(shifted=True, benefit=benefit, cost=cost, debt=debt)
        assert classifier_shift(claim.passage)
        assert positive_information(claim) == (net_information(claim) > 0.0)
        if benefit - cost - debt <= 0.0:
            assert not positive_discovery(claim)
    assert not positive_discovery(discovery_claim(shifted=True, benefit=0.2, cost=0.6, debt=0.2))


def test_unified_positive_discovery_two_audits_exhaustive():
    """thm:philosophy-unified-positive-discovery-two-audits; Lean: BEDC.GroundCompiler.MetricsFlow.forbidden_metric_claims_need_certificates; primitive: positive_discovery, structural_discovery, positive_information; fixture: DiscoveryClaim."""
    for shifted, closed, positive_gain in product((False, True), repeat=3):
        claim = discovery_claim(
            shifted=shifted,
            closed=closed,
            benefit=1.0 if positive_gain else 0.1,
            cost=0.1,
            debt=0.1,
        )
        result = positive_discovery(claim)
        assert result == (structural_discovery(claim.passage) and positive_information(claim) and closed)
        if result:
            assert structural_discovery(claim.passage)
            assert positive_information(claim)
    assert positive_discovery(discovery_claim())


def test_learning_discovery_unified_positive_instance_exhaustive():
    """thm:philosophy-learning-discovery-unified-positive-instance; Lean: BEDC.GroundCompiler.NameCertGenerated.namecert_without_ledger_not_admissible; primitive: positive_discovery; fixture: DiscoveryClaim."""
    for shifted, ledgered, positive_gain in product((False, True), repeat=3):
        claim = discovery_claim(
            shifted=shifted,
            ledgered=ledgered,
            benefit=1.0 if positive_gain else 0.1,
            cost=0.1,
            debt=0.1,
        )
        expected = shifted and ledgered and positive_gain
        assert positive_discovery(claim) == expected
    assert positive_discovery(discovery_claim(shifted=True, ledgered=True, benefit=1.0, cost=0.1, debt=0.1))


def test_interpretability_discovery_unified_positive_instance_exhaustive():
    """thm:philosophy-interpretability-discovery-unified-positive-instance; Lean: BEDC.Derived.KernelAuditWitnessUp.KernelAuditWitnessNameCert_obligations; primitive: ndna_positive_criterion; fixture: DiscoveryClaim."""
    for shifted, ledgered, ndna, positive_gain in product((False, True), repeat=4):
        claim = discovery_claim(
            shifted=shifted,
            ledgered=ledgered,
            ndna=ndna,
            benefit=1.0 if positive_gain else 0.1,
            cost=0.1,
            debt=0.1,
        )
        expected = shifted and ledgered and ndna and positive_gain
        assert ndna_positive_criterion(claim) == expected
    assert ndna_positive_criterion(discovery_claim(ndna=True))


def test_black_box_discovery_resolution_unified_positive_instance_exhaustive():
    """thm:philosophy-black-box-discovery-resolution-unified-positive-instance; Lean: BEDC.FKernel.Gap.Policy.gap_ledgers_not_optional; primitive: positive_discovery_resolution, scoped_resolved; fixture: DiscoveryClaim."""
    for shifted, scoped, black_box, positive_gain in product((False, True), repeat=4):
        claim = discovery_claim(
            shifted=shifted,
            scope_sealed=scoped,
            black_box=black_box,
            benefit=1.0 if positive_gain else 0.1,
            cost=0.1,
            debt=0.1,
        )
        expected = shifted and scoped and black_box and positive_gain
        assert positive_discovery_resolution(claim) == expected
        if expected:
            assert scoped_resolved(claim.scoped_certificate)
    assert positive_discovery_resolution(discovery_claim(black_box=True))


def test_record_growth_hardening_not_unified_positive_discovery_exhaustive():
    """thm:philosophy-record-growth-hardening-not-unified-positive-discovery; Lean: BEDC.GroundCompiler.SourceChannel.ledger_records_distinguish_ordered_pairs; primitive: classifier_shift, local_hardening_delta, positive_discovery; fixture: DiscoveryClaim and HardeningProfile."""
    before = hardening_profile(UnifiedObjectCase(verification_hardened=False, verification_ledgered=True))
    for records, hardened_after in product((2, 3, 8), (False, True)):
        after_case = UnifiedObjectCase(verification_hardened=hardened_after, verification_ledgered=True)
        after = hardening_profile(after_case)
        claim = discovery_claim(shifted=False, benefit=1.0, cost=0.1, debt=0.1)
        grown = classifier_passage(shifted=False, records=records)
        assert not classifier_shift(grown)
        assert not positive_discovery(claim)
        if hardened_after:
            assert local_hardening_delta(before, after) == frozenset({VERIFICATION_ROW})
    assert not positive_discovery(discovery_claim(shifted=False, benefit=1.0, cost=0.1, debt=0.1))


def test_hidden_debt_invalidates_unified_positivity_exhaustive():
    """thm:philosophy-hidden-debt-invalidates-unified-positivity; Lean: BEDC.FKernel.Gap.Policy.gapPolicy_requires_ledger_witness; primitive: apparent_net_information, net_information, positive_discovery; fixture: DiscoveryClaim."""
    for omitted in (0.0, 0.2, 1.0):
        claim = discovery_claim(benefit=1.0, cost=0.1, debt=0.1, omitted_debt=omitted)
        assert apparent_net_information(claim) == 0.8
        assert net_information(claim) == 0.8 - omitted
        assert positive_discovery(claim) == (omitted == 0.0)
    hidden = discovery_claim(benefit=1.0, cost=0.1, debt=0.1, omitted_debt=1.0)
    assert apparent_net_information(hidden) > 0.0
    assert net_information(hidden) <= 0.0
    assert not positive_discovery(hidden)


def test_lineage_axes_separate_exhaustive():
    """thm:philosophy-lineage-axes-separate; Lean: BEDC.FKernel.Gap.Comp.ledger_composition_principle; primitive: classifier_shift, fully_hardened_classifier; fixture: UnifiedObjectCase."""
    cases = (
        {"audit": True, "discovery": False, "positive": False, "hardened": False},
        {"audit": False, "discovery": True, "positive": False, "hardened": False},
        {"audit": True, "discovery": True, "positive": True, "hardened": False},
        {"audit": True, "discovery": False, "positive": False, "hardened": True},
    )
    for lineage in cases:
        case = UnifiedObjectCase(
            verification_hardened=lineage["hardened"],
            verification_ledgered=lineage["hardened"],
        )
        passage = classifier_passage(shifted=lineage["discovery"])
        assert lineage["discovery"] == classifier_shift(passage)
        assert lineage["hardened"] == fully_hardened_classifier(hardening_profile(case), hardening_backend())
        assert set(lineage.values()) != {True}
    assert any(item["audit"] and not item["discovery"] for item in cases)
    assert any(item["discovery"] and not item["positive"] for item in cases)
    assert any(item["positive"] and not item["hardened"] for item in cases)
    assert any(item["hardened"] and not item["discovery"] for item in cases)


def test_unified_closure_theorem_exhaustive():
    """thm:philosophy-unified-closure-theorem; Lean: BEDC.FKernel.NameCert.semanticNameCert_ledger_policy_witness; primitive: ledger_complete, scoped_resolved; fixture: UnifiedObjectCase."""
    for rows in powerset(THEORY_ROWS):
        case = case_from_rows(rows)
        expected = THEORY_ROWS.issubset(rows)
        assert theory_closed(case) == expected
        assert ledger_complete(THEORY_ROWS, recorded_rows(case)) == expected
        if expected:
            assert scoped_resolved(scoped_certificate(case))
        else:
            assert not ledger_complete(THEORY_ROWS, recorded_rows(case))
    assert theory_closed(UnifiedObjectCase())


def test_unified_hardening_theorem_exhaustive():
    """thm:philosophy-unified-hardening-theorem; Lean: BEDC.FKernel.Gap.CompCoverage.hardening_composite_coverage; primitive: fully_hardened_classifier, critical_hardening_gap; fixture: UnifiedObjectCase."""
    backend = hardening_backend()
    for verification_hardened, verification_ledgered, non_hardenable_ledgered, closed in product((False, True), repeat=4):
        case = UnifiedObjectCase(
            ledgered=closed,
            verification_hardened=verification_hardened,
            verification_ledgered=verification_ledgered,
            non_hardenable_ledgered=non_hardenable_ledgered,
        )
        expected = closed and verification_hardened and verification_ledgered and non_hardenable_ledgered
        assert fully_hardened_closed(case) == expected
        assert fully_hardened_classifier(hardening_profile(case), backend) == (
            verification_hardened and verification_ledgered and non_hardenable_ledgered
        )
        if not verification_hardened and not verification_ledgered:
            assert critical_hardening_gap(hardening_profile(case), backend) == frozenset({VERIFICATION_ROW})
    assert fully_hardened_closed(UnifiedObjectCase(verification_hardened=True, verification_ledgered=True))


def test_unified_discovery_theorem_exhaustive():
    """thm:philosophy-unified-discovery-theorem; Lean: BEDC.GroundCompiler.MetricsFlow.forbidden_metric_claims_need_certificates; primitive: classifier_shift, positive_information, positive_discovery; fixture: DiscoveryClaim."""
    for shifted, closed, positive_gain in product((False, True), repeat=3):
        claim = discovery_claim(
            shifted=shifted,
            closed=closed,
            benefit=1.0 if positive_gain else 0.1,
            cost=0.1,
            debt=0.1,
        )
        unified_discovery = classifier_shift(claim.passage) and closed
        unified_positive = unified_discovery and positive_information(claim)
        assert unified_positive == positive_discovery(claim)
        if unified_discovery and not positive_information(claim):
            assert not positive_discovery(claim)
    assert positive_discovery(discovery_claim(shifted=True, closed=True, benefit=1.0, cost=0.1, debt=0.1))


def test_unified_bedc_information_theorem_exhaustive():
    """thm:philosophy-unified-bedc-information-theorem; Lean: BEDC.FKernel.NameCert.SemanticNameCert and BEDC.FKernel.Gap.CompCoverage.hardening_composite_coverage; primitive: structural_discovery, scoped_resolved, fully_hardened_classifier; fixture: UnifiedObjectCase."""
    chain = (
        MATERIAL_ROW,
        CLASSIFIER_ROW,
        NAMECERT_SOURCE_ROW,
        NAMECERT_PATTERN_ROW,
        NAMECERT_CLASSIFIER_ROW,
        NAMECERT_STABILITY_ROW,
        NAMECERT_LEDGER_POLICY_ROW,
        LEDGER_ROW,
        DNA_COMPLETE_ROW,
        DNA_ANCHORED_ROW,
        DNA_COMPATIBLE_ROW,
        SCOPE_ROUTE_ROW,
    )
    for prefix_length in range(len(chain) + 1):
        rows = frozenset(chain[:prefix_length])
        case = case_from_rows(
            rows,
            verification_hardened=True,
            verification_ledgered=True,
            non_hardenable_ledgered=True,
        )
        claim = discovery_claim(shifted=True, closed=theory_closed(case), benefit=1.0, cost=0.1, debt=0.1)
        assert theory_closed(case) == (prefix_length == len(chain))
        if prefix_length < len(chain):
            assert not positive_discovery(claim)
        else:
            assert structural_discovery(claim.passage)
            assert scoped_resolved(scoped_certificate(case))
            assert positive_discovery(claim)
            assert fully_hardened_classifier(hardening_profile(case), hardening_backend())
    record_growth = discovery_claim(shifted=False, benefit=1.0, cost=0.1, debt=0.1)
    assert not structural_discovery(record_growth.passage)
    assert not positive_discovery(record_growth)
