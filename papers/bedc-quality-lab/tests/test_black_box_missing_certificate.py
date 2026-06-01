from dataclasses import dataclass
from itertools import combinations, product

from bedc_quality_lab import discovery
from bedc_quality_lab.classifier_shift import (
    ClassifierPassage,
    ClassifierState,
    classifier_shift,
)
from bedc_quality_lab.ledger import (
    LedgerRowKey,
    ledger_complete,
    ledger_debt,
    ledger_gap,
)
from bedc_quality_lab.metrics import classifier_certificate
from bedc_quality_lab.scope import (
    GlobalResolutionClaim,
    Scope,
    ScopedCertificate,
    global_required_rows,
    globally_resolved,
    scope_rows,
    scoped_resolved,
)


SOURCE_ROW = LedgerRowKey("source", "behavior-domain")
PATTERN_ROW = LedgerRowKey("pattern", "behavior-pattern")
CLASSIFIER_ROW = LedgerRowKey("classifier", "supporting-classifier")
STABILITY_ROW = LedgerRowKey("stability", "scope-stability")
LEDGER_ROW = LedgerRowKey("ledger", "audit-ledger")
FEATURE_LABEL_ROW = LedgerRowKey("semantic", "feature-label")
PROJECTION_ROW = LedgerRowKey("projection-ledger", "visual-compression")
PROBE_CLASSIFIER_ROW = LedgerRowKey("classifier", "probe-classifier")
PROBE_RESIDUE_ROW = LedgerRowKey("ledger", "probe-hidden-residue")
SHIFT_ROW = LedgerRowKey("classifier", "a->b")

NAMECERT_ROWS = frozenset({
    SOURCE_ROW,
    PATTERN_ROW,
    CLASSIFIER_ROW,
    STABILITY_ROW,
    LEDGER_ROW,
})
CERTIFIED = classifier_certificate({
    "linear_identifiability_r2": 0.95,
    "approx_identifiability_proxy": 0.90,
})
UNCERTIFIED = classifier_certificate({
    "linear_identifiability_r2": 0.10,
    "approx_identifiability_proxy": 0.10,
})
BASE_RELATION = frozenset({
    ("a", "a", "same"),
    ("a", "b", "near"),
    ("b", "b", "same"),
})
SHIFTED_RELATION = frozenset({
    ("a", "a", "same"),
    ("a", "b", "far"),
    ("b", "b", "same"),
})


@dataclass(frozen=True)
class BehaviorCase:
    behavior_id: str
    supports: bool
    certificate: dict[str, object]
    required_rows: frozenset[LedgerRowKey]
    recorded_rows: frozenset[LedgerRowKey]
    boundary: frozenset[str] = frozenset({"outside-scope"})


def powerset_rows(rows):
    rows = tuple(rows)
    for size in range(len(rows) + 1):
        for members in combinations(rows, size):
            yield frozenset(members)


def certificate_rows(*rows):
    return frozenset(rows or NAMECERT_ROWS)


def row_costs(rows):
    return {row: 3.0 if row.kind == "ledger" else 1.0 for row in rows}


def lab_scope(behavior_id="B", model_id="M"):
    return Scope(
        domain_ids=frozenset({"D0"}),
        model_id=model_id,
        admitted_family_id="A",
        behavior_id=behavior_id,
    )


def behavior_case(
    *,
    behavior_id="B",
    supports=True,
    certificate=CERTIFIED,
    required_rows=NAMECERT_ROWS,
    recorded_rows=None,
    boundary=frozenset({"outside-scope"}),
):
    return BehaviorCase(
        behavior_id=behavior_id,
        supports=supports,
        certificate=certificate,
        required_rows=required_rows,
        recorded_rows=required_rows if recorded_rows is None else recorded_rows,
        boundary=boundary,
    )


def scoped_certificate(case):
    scope = lab_scope(case.behavior_id)
    required = frozenset(scope_rows(scope) | case.required_rows)
    recorded = frozenset(scope_rows(scope) | case.recorded_rows)
    return ScopedCertificate(
        scope=scope,
        classifier_id="C",
        namecert_id="N",
        required_rows=required,
        recorded_rows=recorded,
        certificate=case.certificate,
        not_claimed_boundary=case.boundary,
    )


def closed_explanation(case):
    cert = scoped_certificate(case)
    return (
        case.supports
        and case.certificate.get("cert_status") == "certified"
        and ledger_complete(cert.required_rows, cert.recorded_rows)
        and scoped_resolved(cert)
    )


def black_box_behavior(case):
    return case.supports and not closed_explanation(case)


def unexplained_behavior(case):
    return not case.supports


def state(*, shifted=False, certificate=CERTIFIED):
    return ClassifierState(
        source_ids=frozenset({"a", "b"}),
        pattern_id="black-box-resolution",
        ledger_policy=frozenset({SHIFT_ROW}),
        relation=SHIFTED_RELATION if shifted else BASE_RELATION,
        certificate=certificate,
        surface_used=frozenset({("a", "b")}),
    )


def passage(*, shifted=False, certificate=CERTIFIED, recorded_rows=frozenset({SHIFT_ROW})):
    return ClassifierPassage(
        source=state(shifted=False),
        target=state(shifted=shifted, certificate=certificate),
        recorded_rows=recorded_rows,
    )


def discovery_scoped_cert(*, certificate=CERTIFIED, recorded_rows=None, boundary=frozenset({"outside-scope"})):
    case = behavior_case(certificate=certificate, recorded_rows=NAMECERT_ROWS if recorded_rows is None else recorded_rows, boundary=boundary)
    return scoped_certificate(case)


def discovery_claim(
    *,
    shifted=True,
    certificate=CERTIFIED,
    passage_rows=frozenset({SHIFT_ROW}),
    claim_rows=frozenset({SHIFT_ROW}),
    required_rows=frozenset({SHIFT_ROW}),
    scope_sealed=True,
    scoped_cert=None,
    boundary=frozenset({"outside-scope"}),
    black_box_debt_reduction=0.0,
    black_box_score_cost=0.0,
):
    cert = discovery_scoped_cert(certificate=certificate, boundary=boundary) if scoped_cert is None else scoped_cert
    return discovery.DiscoveryClaim(
        passage=passage(
            shifted=shifted,
            certificate=certificate,
            recorded_rows=passage_rows,
        ),
        benefit_terms={"coverage": 1.0},
        score_terms={"classifier": 0.1},
        debt_terms={"ledger": 0.1},
        ledger_required_rows=required_rows,
        ledger_recorded_rows=claim_rows,
        public_cost_protocol=True,
        scope_sealed=scope_sealed,
        not_claimed_boundary=boundary,
        scoped_certificate=cert,
        black_box_debt_reduction=black_box_debt_reduction,
        black_box_score_cost=black_box_score_cost,
    )


def global_claim_for(certificates, recorded_rows=frozenset(), behavior_family=None):
    family = (
        frozenset(cert.scope.behavior_id for cert in certificates)
        if behavior_family is None
        else behavior_family
    )
    return GlobalResolutionClaim(
        model_id="M",
        behavior_family=family,
        certificates=tuple(certificates),
        global_recorded_rows=recorded_rows,
    )


def full_global_claim(certificates, behavior_family=None):
    base = global_claim_for(certificates, behavior_family=behavior_family)
    return global_claim_for(
        certificates,
        behavior_family=base.behavior_family,
        recorded_rows=global_required_rows(base),
    )


def test_black_boxes_have_support_structure_exhaustive():
    """thm:philosophy-black-boxes-have-support-structure; Lean: BEDC.FKernel.NameCert.SemanticNameCert; primitive: classifier_certificate, ledger_gap."""
    for supports, certificate, recorded_rows in product(
        (False, True),
        (UNCERTIFIED, CERTIFIED),
        powerset_rows(NAMECERT_ROWS),
    ):
        case = behavior_case(
            supports=supports,
            certificate=certificate,
            recorded_rows=recorded_rows,
        )
        if black_box_behavior(case):
            assert case.supports
            assert ledger_gap(case.required_rows, case.recorded_rows) or certificate["cert_status"] != "certified"

    positive = behavior_case(recorded_rows=NAMECERT_ROWS - {LEDGER_ROW})
    counter = behavior_case(supports=False, recorded_rows=frozenset())
    assert black_box_behavior(positive) and positive.supports
    assert not black_box_behavior(counter) and unexplained_behavior(counter)


def test_unexplained_not_black_box_exhaustive():
    """thm:philosophy-unexplained-not-black-box; Lean: BEDC.FKernel.NameCert.NameCert; primitive: ledger_gap."""
    for certificate, recorded_rows in product((UNCERTIFIED, CERTIFIED), powerset_rows(NAMECERT_ROWS)):
        case = behavior_case(
            supports=False,
            certificate=certificate,
            recorded_rows=recorded_rows,
        )
        assert unexplained_behavior(case)
        assert not black_box_behavior(case)

    unexplained = behavior_case(supports=False, recorded_rows=frozenset())
    black_box = behavior_case(supports=True, recorded_rows=frozenset())
    assert unexplained_behavior(unexplained) and not black_box_behavior(unexplained)
    assert black_box_behavior(black_box) and not unexplained_behavior(black_box)


def test_closed_explanation_not_black_box_exhaustive():
    """thm:philosophy-closed-explanation-not-black-box; Lean: BEDC.Meta.DiscoveryCertificate.NameCertFiveRows; primitive: classifier_certificate, ledger_complete, scoped_resolved."""
    for certificate, recorded_rows, boundary in product(
        (UNCERTIFIED, CERTIFIED),
        powerset_rows(NAMECERT_ROWS),
        (frozenset(), frozenset({"outside"})),
    ):
        case = behavior_case(
            certificate=certificate,
            recorded_rows=recorded_rows,
            boundary=boundary,
        )
        if closed_explanation(case):
            assert not black_box_behavior(case)
            assert certificate["cert_status"] == "certified"
            assert ledger_complete(scoped_certificate(case).required_rows, scoped_certificate(case).recorded_rows)

    closed = behavior_case()
    counter = behavior_case(recorded_rows=NAMECERT_ROWS - {LEDGER_ROW})
    assert closed_explanation(closed) and not black_box_behavior(closed)
    assert black_box_behavior(counter) and not closed_explanation(counter)


def test_missing_namecert_rows_diagnose_black_boxes_exhaustive():
    """thm:philosophy-missing-namecert-rows-diagnose-black-boxes; Lean: BEDC.Meta.DiscoveryCertificate.nameCertFiveRows_pattern_ledger; primitive: ledger_gap, ledger_complete."""
    for recorded_rows in powerset_rows(NAMECERT_ROWS):
        gap = ledger_gap(NAMECERT_ROWS, recorded_rows)
        case = behavior_case(recorded_rows=recorded_rows)
        assert bool(gap) == (not ledger_complete(NAMECERT_ROWS, recorded_rows))
        if gap:
            assert black_box_behavior(case)
            assert not closed_explanation(case)

    for row in NAMECERT_ROWS:
        missing_one = NAMECERT_ROWS - {row}
        assert row in ledger_gap(NAMECERT_ROWS, missing_one)
    assert not ledger_gap(NAMECERT_ROWS, NAMECERT_ROWS)


def test_ledger_black_box_high_risk_exhaustive():
    """thm:philosophy-ledger-black-box-high-risk; Lean: BEDC.Meta.DiscoveryCertificate.discoveryRows_after_ledger; primitive: ledger_complete, ledger_gap."""
    rich_rows = NAMECERT_ROWS - {LEDGER_ROW}
    for extra_rows in powerset_rows((FEATURE_LABEL_ROW, PROJECTION_ROW, PROBE_CLASSIFIER_ROW)):
        recorded_rows = rich_rows | extra_rows
        case = behavior_case(recorded_rows=recorded_rows)
        assert SOURCE_ROW in recorded_rows
        assert PATTERN_ROW in recorded_rows
        assert CLASSIFIER_ROW in recorded_rows
        assert STABILITY_ROW in recorded_rows
        assert LEDGER_ROW in ledger_gap(NAMECERT_ROWS, recorded_rows)
        assert not ledger_complete(NAMECERT_ROWS, recorded_rows)
        assert black_box_behavior(case)

    counter = behavior_case(recorded_rows=NAMECERT_ROWS)
    assert closed_explanation(counter)
    assert not black_box_behavior(counter)


def test_closed_explanations_zero_deficit_exhaustive():
    """thm:philosophy-closed-explanations-zero-deficit; Lean: BEDC.FKernel.NameCert.semanticNameCert_ledger_policy_witness; primitive: ledger_gap, ledger_debt."""
    costs = row_costs(NAMECERT_ROWS)
    for recorded_rows in powerset_rows(NAMECERT_ROWS):
        gap = ledger_gap(NAMECERT_ROWS, recorded_rows)
        debt = ledger_debt(gap, costs)
        assert (not gap and debt == 0.0) == ledger_complete(NAMECERT_ROWS, recorded_rows)

    closed = behavior_case(recorded_rows=NAMECERT_ROWS)
    counter = behavior_case(recorded_rows=NAMECERT_ROWS - {LEDGER_ROW})
    assert ledger_debt(ledger_gap(closed.required_rows, closed.recorded_rows), costs) == 0.0
    assert ledger_debt(ledger_gap(counter.required_rows, counter.recorded_rows), costs) > 0.0


def test_black_box_debt_can_decrease_before_closure_exhaustive():
    """thm:philosophy-black-box-debt-can-decrease-before-closure; Lean: BEDC.Meta.DiscoveryCertificate.discovery_debt_witness; primitive: ledger_debt, ledger_complete."""
    costs = row_costs(NAMECERT_ROWS)
    partial_pairs = 0
    for before_rows, after_rows in product(powerset_rows(NAMECERT_ROWS), repeat=2):
        before_gap = ledger_gap(NAMECERT_ROWS, before_rows)
        after_gap = ledger_gap(NAMECERT_ROWS, after_rows)
        before_debt = ledger_debt(before_gap, costs)
        after_debt = ledger_debt(after_gap, costs)
        if before_rows < after_rows and not ledger_complete(NAMECERT_ROWS, after_rows):
            partial_pairs += 1
            assert after_debt < before_debt

    before = behavior_case(recorded_rows=frozenset({SOURCE_ROW}))
    after = behavior_case(recorded_rows=frozenset({SOURCE_ROW, CLASSIFIER_ROW, STABILITY_ROW}))
    assert partial_pairs > 0
    assert ledger_debt(ledger_gap(NAMECERT_ROWS, after.recorded_rows), costs) < ledger_debt(ledger_gap(NAMECERT_ROWS, before.recorded_rows), costs)
    assert not closed_explanation(after)


def test_scoped_resolution_by_namecert_exhaustive():
    """thm:philosophy-scoped-resolution-by-namecert; Lean: BEDC.Meta.DiscoveryCertificate.after_state_semantic_namecert; primitive: ScopedCertificate, scoped_resolved."""
    required = NAMECERT_ROWS
    for certificate, recorded_rows, boundary in product(
        (UNCERTIFIED, CERTIFIED),
        powerset_rows(required),
        (frozenset(), frozenset({"outside"})),
    ):
        case = behavior_case(
            certificate=certificate,
            recorded_rows=recorded_rows,
            boundary=boundary,
        )
        cert = scoped_certificate(case)
        expected = (
            certificate["cert_status"] == "certified"
            and cert.required_rows.issubset(cert.recorded_rows)
            and bool(boundary)
        )
        assert scoped_resolved(cert) == expected

    positive = scoped_certificate(behavior_case())
    counter = scoped_certificate(behavior_case(recorded_rows=required - {LEDGER_ROW}))
    assert scoped_resolved(positive)
    assert not scoped_resolved(counter)


def test_global_resolution_requires_global_ledger_exhaustive():
    """thm:philosophy-global-resolution-requires-global-ledger; Lean: BEDC.FKernel.NameCert.semanticNameCert_pattern_ledger_witness; primitive: GlobalResolutionClaim, global_required_rows, globally_resolved."""
    cert = scoped_certificate(behavior_case())
    full = full_global_claim((cert,))
    required = global_required_rows(full)

    for recorded_rows in powerset_rows(required):
        candidate = global_claim_for((cert,), recorded_rows=recorded_rows)
        assert globally_resolved(candidate) == required.issubset(recorded_rows)

    missing_global = global_claim_for(
        (cert,),
        recorded_rows=required - {LedgerRowKey("global-ledger", "M")},
    )
    assert not globally_resolved(missing_global)
    assert globally_resolved(full)


def test_interpretability_claims_scoped_default_exhaustive():
    """cor:philosophy-interpretability-claims-scoped-default; Lean: BEDC.FKernel.NameCert.SemanticNameCert; primitive: scoped_resolved, globally_resolved, global_required_rows."""
    local_rows = (
        FEATURE_LABEL_ROW,
        PROJECTION_ROW,
        PROBE_CLASSIFIER_ROW,
        PROBE_RESIDUE_ROW,
    )
    cert = scoped_certificate(behavior_case())
    assert scoped_resolved(cert)

    for evidence_rows in powerset_rows(local_rows):
        claim = global_claim_for(
            (cert,),
            recorded_rows=cert.recorded_rows | evidence_rows,
        )
        assert not globally_resolved(claim)

    full = full_global_claim((cert,))
    scoped_only = global_claim_for((cert,), recorded_rows=cert.recorded_rows | frozenset(local_rows))
    assert not globally_resolved(scoped_only)
    assert globally_resolved(full)


def test_feature_labels_do_not_resolve_black_boxes_exhaustive():
    """thm:philosophy-feature-labels-do-not-resolve-black-boxes; Lean: BEDC.Meta.DiscoveryCertificate.NameCertFiveRows; primitive: ledger_gap, ledger_complete."""
    optional_labels = (FEATURE_LABEL_ROW,)
    for label_rows, namecert_rows in product(powerset_rows(optional_labels), powerset_rows((SOURCE_ROW, PATTERN_ROW))):
        recorded_rows = label_rows | namecert_rows
        gap = ledger_gap(NAMECERT_ROWS, recorded_rows)
        assert FEATURE_LABEL_ROW not in NAMECERT_ROWS
        assert gap
        assert not ledger_complete(NAMECERT_ROWS, recorded_rows)
        assert black_box_behavior(behavior_case(recorded_rows=recorded_rows))

    label_only = behavior_case(recorded_rows=frozenset({FEATURE_LABEL_ROW}))
    closed = behavior_case(recorded_rows=NAMECERT_ROWS)
    assert black_box_behavior(label_only)
    assert not black_box_behavior(closed)


def test_visual_explanations_require_projection_ledger_exhaustive():
    """thm:philosophy-visual-explanations-require-projection-ledger; Lean: BEDC.Meta.DiscoveryCertificate.nameCertFiveRows_ledger; primitive: ledger_gap, scoped_resolved."""
    required = NAMECERT_ROWS | {PROJECTION_ROW}
    for recorded_rows in powerset_rows(required):
        case = behavior_case(required_rows=required, recorded_rows=recorded_rows)
        cert = scoped_certificate(case)
        if PROJECTION_ROW not in recorded_rows:
            assert PROJECTION_ROW in ledger_gap(required, recorded_rows)
            assert not scoped_resolved(cert)
        else:
            assert scoped_resolved(cert) == required.issubset(recorded_rows)

    positive = behavior_case(required_rows=required, recorded_rows=required)
    counter = behavior_case(required_rows=required, recorded_rows=required - {PROJECTION_ROW})
    assert closed_explanation(positive)
    assert black_box_behavior(counter)


def test_probe_explanations_require_probe_ledger_exhaustive():
    """thm:philosophy-probe-explanations-require-probe-ledger; Lean: BEDC.Meta.DiscoveryCertificate.discoveryRows_after_pattern_ledger; primitive: ledger_gap, ledger_complete."""
    required = NAMECERT_ROWS | {PROBE_CLASSIFIER_ROW, PROBE_RESIDUE_ROW}
    for recorded_rows in powerset_rows(required):
        gap = ledger_gap(required, recorded_rows)
        expected_closed = required.issubset(recorded_rows)
        case = behavior_case(required_rows=required, recorded_rows=recorded_rows)
        assert ledger_complete(required, recorded_rows) == expected_closed
        if PROBE_CLASSIFIER_ROW not in recorded_rows or PROBE_RESIDUE_ROW not in recorded_rows:
            assert PROBE_CLASSIFIER_ROW in gap or PROBE_RESIDUE_ROW in gap
            assert not closed_explanation(case)

    positive = behavior_case(required_rows=required, recorded_rows=required)
    counter = behavior_case(required_rows=required, recorded_rows=required - {PROBE_RESIDUE_ROW})
    assert closed_explanation(positive)
    assert black_box_behavior(counter)


def test_black_box_reduction_not_necessarily_discovery_exhaustive():
    """thm:philosophy-black-box-reduction-not-necessarily-discovery; Lean: BEDC.Meta.DiscoveryCertificate.discovery_transition_witness; primitive: positive_black_box_resolution, positive_discovery, classifier_shift."""
    for shifted, reduction, cost in product((False, True), (0.0, 0.4, 1.0), (0.0, 0.5)):
        candidate = discovery_claim(
            shifted=shifted,
            black_box_debt_reduction=reduction,
            black_box_score_cost=cost,
        )
        if discovery.positive_black_box_resolution(candidate) and not classifier_shift(candidate.passage):
            assert not discovery.positive_discovery(candidate)

    reduction_only = discovery_claim(
        shifted=False,
        black_box_debt_reduction=1.0,
        black_box_score_cost=0.1,
    )
    discovery_case = discovery_claim(
        shifted=True,
        black_box_debt_reduction=1.0,
        black_box_score_cost=0.1,
    )
    assert discovery.positive_black_box_resolution(reduction_only)
    assert not classifier_shift(reduction_only.passage)
    assert not discovery.positive_discovery(reduction_only)
    assert discovery.positive_discovery_resolution(discovery_case)


def test_black_box_resolution_may_contain_discovery_exhaustive():
    """thm:philosophy-black-box-resolution-may-contain-discovery; Lean: BEDC.Meta.DiscoveryCertificate.DiscoveryTransition; primitive: positive_discovery_resolution, positive_discovery, classifier_shift, ledger_complete."""
    for shifted, certificate, passage_rows, claim_rows, scope_sealed in product(
        (False, True),
        (UNCERTIFIED, CERTIFIED),
        powerset_rows((SHIFT_ROW,)),
        powerset_rows((SHIFT_ROW,)),
        (False, True),
    ):
        candidate = discovery_claim(
            shifted=shifted,
            certificate=certificate,
            passage_rows=passage_rows,
            claim_rows=claim_rows,
            scope_sealed=scope_sealed,
            black_box_debt_reduction=1.0,
            black_box_score_cost=0.1,
        )
        if discovery.positive_discovery_resolution(candidate):
            assert classifier_shift(candidate.passage)
            assert discovery.positive_discovery(candidate)
            assert discovery.positive_black_box_resolution(candidate)
            assert ledger_complete(candidate.ledger_required_rows, candidate.ledger_recorded_rows)

    positive = discovery_claim(
        shifted=True,
        black_box_debt_reduction=1.0,
        black_box_score_cost=0.1,
    )
    counter = discovery_claim(
        shifted=True,
        certificate=UNCERTIFIED,
        black_box_debt_reduction=1.0,
        black_box_score_cost=0.1,
    )
    assert discovery.positive_discovery_resolution(positive)
    assert not discovery.positive_discovery_resolution(counter)


def test_black_box_missing_certificate_theorem_exhaustive():
    """thm:philosophy-black-box-missing-certificate-theorem; Lean: BEDC.FKernel.NameCert.NameCert and BEDC.Meta.DiscoveryCertificate.NameCertFiveRows; primitive: classifier_certificate, ledger_complete, scoped_resolved."""
    cases = []
    for supports, certificate, recorded_rows in product(
        (False, True),
        (UNCERTIFIED, CERTIFIED),
        powerset_rows(NAMECERT_ROWS),
    ):
        case = behavior_case(
            supports=supports,
            certificate=certificate,
            recorded_rows=recorded_rows,
        )
        states = (
            unexplained_behavior(case),
            black_box_behavior(case),
            closed_explanation(case),
        )
        assert sum(bool(state) for state in states) == 1
        cases.append(states)

    unexplained = behavior_case(supports=False, recorded_rows=frozenset())
    black_box = behavior_case(supports=True, certificate=UNCERTIFIED, recorded_rows=NAMECERT_ROWS)
    closed = behavior_case(supports=True, certificate=CERTIFIED, recorded_rows=NAMECERT_ROWS)
    assert (unexplained_behavior(unexplained), black_box_behavior(unexplained), closed_explanation(unexplained)) == (True, False, False)
    assert (unexplained_behavior(black_box), black_box_behavior(black_box), closed_explanation(black_box)) == (False, True, False)
    assert (unexplained_behavior(closed), black_box_behavior(closed), closed_explanation(closed)) == (False, False, True)
    assert {(True, False, False), (False, True, False), (False, False, True)}.issubset(set(cases))
