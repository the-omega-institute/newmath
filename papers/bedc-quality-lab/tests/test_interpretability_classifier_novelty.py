from dataclasses import dataclass, field
from itertools import combinations, product
from typing import Mapping

from bedc_quality_lab import discovery
from bedc_quality_lab.classifier_shift import (
    ClassifierPassage,
    ClassifierState,
    classifier_shift,
    classifier_surface_delta,
    structural_discovery,
)
from bedc_quality_lab.hardening import HardeningBackend, HardeningProfile, critical_hardening_gap, fully_hardened_classifier
from bedc_quality_lab.ledger import LedgerEntry, LedgerRowKey, critical_gap, ledger_complete, ledger_debt, ledger_gap
from bedc_quality_lab.metrics import classifier_certificate
from bedc_quality_lab.scope import Scope, ScopedCertificate, scope_rows


RelationRow = tuple[str, str, str]
SurfacePair = tuple[str, str]

SOURCE_IDS = frozenset({"a", "b", "c"})
PAIR_AB = ("a", "b")
PAIR_AC = ("a", "c")
PAIR_BC = ("b", "c")
ROW_AB = LedgerRowKey("classifier", "a->b")
ROW_AC = LedgerRowKey("classifier", "a->c")
LEDGER_ROW = LedgerRowKey("ledger", "boundary-clarification")
VERIFY_ROW = LedgerRowKey("verification", "kernel-hardening")
SEMANTIC_ROW = LedgerRowKey("semantic", "label-boundary")
NDNA_ROW = LedgerRowKey("ndna", "classifier-locus")
POLICY_AB = frozenset({ROW_AB})
POLICY_AB_AC = frozenset({ROW_AB, ROW_AC})
SURFACE_AB = frozenset({PAIR_AB})
SURFACE_AB_AC = frozenset({PAIR_AB, PAIR_AC})
SELF_RELATION = frozenset({("a", "a", "same"), ("b", "b", "same"), ("c", "c", "same")})
AB_RELATION = frozenset({("a", "b", "same")})
AC_RELATION = frozenset({("a", "c", "same")})
BASE_RELATION = SELF_RELATION | AB_RELATION
REFINED_RELATION = SELF_RELATION
REORGANIZED_RELATION = SELF_RELATION | AC_RELATION
CERTIFIED = classifier_certificate({"linear_identifiability_r2": 0.95, "approx_identifiability_proxy": 0.90})
UNCERTIFIED = classifier_certificate({"linear_identifiability_r2": 0.10, "approx_identifiability_proxy": 0.10})


@dataclass(frozen=True)
class NoveltyProjectionCase:
    source_relation: frozenset[RelationRow] = BASE_RELATION
    target_relation: frozenset[RelationRow] = REFINED_RELATION
    surface_used: frozenset[SurfacePair] = SURFACE_AB
    certificate: Mapping[str, object] = field(default_factory=lambda: CERTIFIED)
    ledger_policy: frozenset[LedgerRowKey] = POLICY_AB
    passage_rows: frozenset[LedgerRowKey] = POLICY_AB
    claim_rows: frozenset[LedgerRowKey] = POLICY_AB
    required_rows: frozenset[LedgerRowKey] = POLICY_AB
    benefit_terms: Mapping[str, float] = field(default_factory=lambda: {"coverage": 1.0})
    score_terms: Mapping[str, float] = field(default_factory=lambda: {"audit": 0.1})
    debt_terms: Mapping[str, float] = field(default_factory=lambda: {"ledger": 0.1})
    boundary: frozenset[str] = frozenset({"outside-classifier"})
    scope_sealed: bool = True
    hardening_profile: HardeningProfile | None = None
    hardening_backend: HardeningBackend | None = None
    ndna_classifier_locus: bool = False
    ndna_nonclassifier_locus: bool = False
    ndna_complete: bool = False
    ndna_anchored: bool = False
    ndna_namecert_compatible: bool = False
    ndna_ledger_complete: bool = False
    ndna_net_information: float = 0.0
    local_or_formal_witness: bool = True
    verification_assisted: bool = False
    verification_benefit: float = 0.0


def powerset(values):
    values = tuple(values)
    for size in range(len(values) + 1):
        for members in combinations(values, size):
            yield frozenset(members)


def _state(
    relation: frozenset[RelationRow],
    *,
    certificate: Mapping[str, object] = CERTIFIED,
    ledger_policy: frozenset[LedgerRowKey] = POLICY_AB,
    surface_used: frozenset[SurfacePair] = SURFACE_AB,
    verification_status: str = "unverified",
    record_count: int = 0,
    feature_count: int = 0,
    notation: str = "plain",
) -> ClassifierState:
    return ClassifierState(
        source_ids=SOURCE_IDS,
        pattern_id="interpretability-classifier-novelty",
        ledger_policy=ledger_policy,
        relation=relation,
        certificate=certificate,
        surface_used=surface_used,
        verification_status=verification_status,
        record_count=record_count,
        feature_count=feature_count,
        notation=notation,
    )


def _target_relation(item: NoveltyProjectionCase) -> frozenset[RelationRow]:
    if item.ndna_nonclassifier_locus:
        return item.source_relation
    return item.target_relation


def _surface_used(item: NoveltyProjectionCase) -> frozenset[SurfacePair]:
    if item.ndna_classifier_locus:
        return item.surface_used | SURFACE_AB
    if item.ndna_nonclassifier_locus:
        return frozenset()
    return item.surface_used


def _passage(item: NoveltyProjectionCase) -> ClassifierPassage:
    return ClassifierPassage(
        source=_state(item.source_relation),
        target=_state(
            _target_relation(item),
            certificate=item.certificate,
            ledger_policy=item.ledger_policy,
            surface_used=_surface_used(item),
        ),
        recorded_rows=item.passage_rows,
    )


def _scope_cert(
    *,
    certificate: Mapping[str, object] = CERTIFIED,
    required_rows: frozenset[LedgerRowKey] = POLICY_AB,
    recorded_rows: frozenset[LedgerRowKey] = POLICY_AB,
    boundary: frozenset[str] = frozenset({"outside-classifier"}),
) -> ScopedCertificate:
    scope = Scope(frozenset({"trace"}), "model", "interpretability-family", "classifier-novelty")
    scope_required = scope_rows(scope) | required_rows
    scope_recorded = scope_rows(scope) | recorded_rows
    return ScopedCertificate(scope, "classifier", "namecert", scope_required, scope_recorded, certificate, boundary)


def _claim(item: NoveltyProjectionCase = NoveltyProjectionCase()) -> discovery.DiscoveryClaim:
    return discovery.DiscoveryClaim(
        passage=_passage(item),
        benefit_terms=item.benefit_terms,
        score_terms=item.score_terms,
        debt_terms=item.debt_terms,
        ledger_required_rows=item.required_rows,
        ledger_recorded_rows=item.claim_rows,
        public_cost_protocol=True,
        scope_sealed=item.scope_sealed,
        not_claimed_boundary=item.boundary,
        local_or_formal_witness=item.local_or_formal_witness,
        scoped_certificate=_scope_cert(
            certificate=item.certificate,
            required_rows=item.required_rows,
            recorded_rows=item.claim_rows,
            boundary=item.boundary,
        ),
        hardening_profile=item.hardening_profile,
        hardening_backend=item.hardening_backend,
        ndna_complete=item.ndna_complete,
        ndna_anchored=item.ndna_anchored,
        ndna_namecert_compatible=item.ndna_namecert_compatible,
        ndna_ledger_complete=item.ndna_ledger_complete,
        ndna_net_information=item.ndna_net_information,
        verification_assisted=item.verification_assisted,
        verification_benefit=item.verification_benefit,
        verification_required_rows=frozenset({VERIFY_ROW}) if item.verification_assisted else frozenset(),
        verification_recorded_rows=frozenset({VERIFY_ROW}) if item.verification_assisted else frozenset(),
    )


def _relation_for_pairs(pairs: frozenset[SurfacePair]) -> frozenset[RelationRow]:
    rows = set(SELF_RELATION)
    if PAIR_AB in pairs:
        rows.add(("a", "b", "same"))
    if PAIR_AC in pairs:
        rows.add(("a", "c", "same"))
    if PAIR_BC in pairs:
        rows.add(("b", "c", "same"))
    return frozenset(rows)


def _strict_refinement(source: frozenset[RelationRow], target: frozenset[RelationRow]) -> bool:
    return target < source


def _strict_coarsening(source: frozenset[RelationRow], target: frozenset[RelationRow]) -> bool:
    return source < target


def _reorganization(source: frozenset[RelationRow], target: frozenset[RelationRow]) -> bool:
    return source != target and not _strict_refinement(source, target) and not _strict_coarsening(source, target)


def _hardening_profile(
    *,
    hardened: bool = True,
    recorded: bool = True,
    certificate: Mapping[str, object] = CERTIFIED,
) -> HardeningProfile:
    rows = frozenset({VERIFY_ROW})
    recorded_rows = rows if recorded else frozenset()
    hardened_rows = rows if hardened else frozenset()
    return HardeningProfile(certificate, rows, rows, frozenset(), rows, recorded_rows, rows, hardened_rows, frozenset(), frozenset())


def test_philosophy_local_witness_gives_classifier_novelty_exhaustive():
    """thm:philosophy-local-witness-gives-classifier-novelty; Lean: BEDC.Meta.DiscoveryCertificate.classifierNonEquivalent_not_equivalentOn; primitive: classifier_surface_delta, classifier_shift."""
    for target_relation, rows in product((BASE_RELATION, REFINED_RELATION, REORGANIZED_RELATION), powerset((ROW_AB,))):
        passage = _passage(NoveltyProjectionCase(target_relation=target_relation, passage_rows=rows))
        if classifier_surface_delta(passage):
            assert classifier_shift(passage)
    assert classifier_shift(_passage(NoveltyProjectionCase(target_relation=REFINED_RELATION)))
    assert not classifier_shift(_passage(NoveltyProjectionCase(target_relation=BASE_RELATION)))


def test_philosophy_one_pair_certifies_non_equivalence_exhaustive():
    """cor:philosophy-one-pair-certifies-non-equivalence; Lean: BEDC.Meta.DiscoveryCertificate.classifierNonEquivalent_not_equivalentOn; primitive: classifier_shift."""
    judgments = (frozenset(), AB_RELATION)
    for before, after in product(judgments, repeat=2):
        passage = _passage(NoveltyProjectionCase(source_relation=SELF_RELATION | before, target_relation=SELF_RELATION | after))
        assert classifier_shift(passage) == (before != after)
    assert classifier_shift(_passage(NoveltyProjectionCase(source_relation=SELF_RELATION, target_relation=SELF_RELATION | AB_RELATION)))
    assert not classifier_shift(_passage(NoveltyProjectionCase(source_relation=SELF_RELATION, target_relation=SELF_RELATION)))


def test_philosophy_feature_side_change_no_classifier_novelty_exhaustive():
    """thm:philosophy-feature-side-change-no-classifier-novelty; Lean: BEDC.Meta.ClassifierIncrement.MechanicalComputation; primitive: classifier_shift, structural_discovery."""
    for feature_count, certificate, rows in product((0, 1, 5), (UNCERTIFIED, CERTIFIED), powerset((ROW_AB,))):
        passage = ClassifierPassage(
            _state(BASE_RELATION),
            _state(BASE_RELATION, certificate=certificate, feature_count=feature_count),
            rows,
        )
        assert not classifier_shift(passage)
        assert not structural_discovery(passage)
    assert not classifier_shift(_passage(NoveltyProjectionCase(target_relation=BASE_RELATION)))
    assert structural_discovery(_passage(NoveltyProjectionCase(target_relation=REFINED_RELATION)))


def test_philosophy_circuit_side_change_no_classifier_novelty_exhaustive():
    """thm:philosophy-circuit-side-change-no-classifier-novelty; Lean: BEDC.GroundCompiler.AnalysisPipeline.StageLedgerAudit; primitive: classifier_shift, structural_discovery."""
    for notation, record_count, surface in product(("plain", "route-audit"), (0, 3), (frozenset(), SURFACE_AB)):
        passage = ClassifierPassage(
            _state(BASE_RELATION),
            _state(BASE_RELATION, notation=notation, record_count=record_count, surface_used=surface),
            POLICY_AB,
        )
        assert not classifier_shift(passage)
        assert not structural_discovery(passage)
    assert not structural_discovery(_passage(NoveltyProjectionCase(target_relation=BASE_RELATION, surface_used=frozenset())))
    assert structural_discovery(_passage(NoveltyProjectionCase(target_relation=REFINED_RELATION, surface_used=SURFACE_AB)))


def test_philosophy_ledger_repair_no_classifier_novelty_exhaustive():
    """thm:philosophy-ledger-repair-no-classifier-novelty; Lean: BEDC.GroundCompiler.ChapterFlow.LedgerSound; primitive: ledger_gap, ledger_debt, classifier_shift."""
    costs = {ROW_AB: 2.0, LEDGER_ROW: 1.0}
    required = frozenset({ROW_AB, LEDGER_ROW})
    for rows in powerset(required):
        passage = _passage(NoveltyProjectionCase(target_relation=BASE_RELATION, ledger_policy=required, passage_rows=rows))
        assert ledger_debt(ledger_gap(required, rows), costs) >= 0.0
        assert not classifier_shift(passage)
        assert not structural_discovery(passage)
    assert ledger_debt(ledger_gap(required, required), costs) == 0.0
    assert structural_discovery(_passage(NoveltyProjectionCase(target_relation=REFINED_RELATION, ledger_policy=POLICY_AB, passage_rows=POLICY_AB)))


def test_philosophy_hardening_semantic_no_classifier_novelty_exhaustive():
    """thm:philosophy-hardening-semantic-no-classifier-novelty; Lean: BEDC.GroundCompiler.AnalysisPipeline.CertificateObligationDischarge; primitive: fully_hardened_classifier, classifier_shift."""
    backend = HardeningBackend("lean", frozenset({VERIFY_ROW}))
    for hardened, semantic_rows in product((False, True), powerset((SEMANTIC_ROW,))):
        profile = _hardening_profile(hardened=hardened, recorded=True)
        passage = _passage(NoveltyProjectionCase(target_relation=BASE_RELATION, passage_rows=POLICY_AB | semantic_rows))
        assert not classifier_shift(passage)
        if hardened:
            assert fully_hardened_classifier(profile, backend)
    assert not classifier_shift(_passage(NoveltyProjectionCase(target_relation=BASE_RELATION)))
    assert classifier_shift(_passage(NoveltyProjectionCase(target_relation=REFINED_RELATION)))


def test_philosophy_improvement_discovery_distinct_exhaustive():
    """cor:philosophy-improvement-discovery-distinct; Lean: BEDC.Meta.ClassifierIncrement.PositiveDiscovery; primitive: positive_information, positive_discovery."""
    for benefit, rows in product((0.4, 1.0, 2.0), powerset((LEDGER_ROW,))):
        claim = _claim(
            NoveltyProjectionCase(
                target_relation=BASE_RELATION,
                benefit_terms={"audit": benefit},
                passage_rows=POLICY_AB | rows,
                claim_rows=POLICY_AB | rows,
                required_rows=POLICY_AB,
            )
        )
        assert discovery.positive_information(claim)
        assert not discovery.positive_discovery(claim)
    assert not discovery.positive_discovery(_claim(NoveltyProjectionCase(target_relation=BASE_RELATION, benefit_terms={"audit": 2.0})))
    assert discovery.positive_discovery(_claim(NoveltyProjectionCase(target_relation=REFINED_RELATION, benefit_terms={"coverage": 2.0})))


def test_philosophy_refinement_creates_classifier_novelty_exhaustive():
    """thm:philosophy-refinement-creates-classifier-novelty; Lean: BEDC.Meta.ClassifierIncrement.StructuralDiscovery; primitive: classifier_shift, structural_discovery."""
    pair_sets = tuple(powerset((PAIR_AB, PAIR_AC)))
    for source_pairs, target_pairs in product(pair_sets, repeat=2):
        source = _relation_for_pairs(source_pairs)
        target = _relation_for_pairs(target_pairs)
        if _strict_refinement(source, target):
            changed_rows = frozenset({ROW_AB for pair in source_pairs ^ target_pairs if pair == PAIR_AB} | {ROW_AC for pair in source_pairs ^ target_pairs if pair == PAIR_AC})
            passage = _passage(NoveltyProjectionCase(source_relation=source, target_relation=target, surface_used=SURFACE_AB_AC, ledger_policy=changed_rows, passage_rows=changed_rows))
            assert classifier_shift(passage)
    assert structural_discovery(_passage(NoveltyProjectionCase(source_relation=BASE_RELATION, target_relation=REFINED_RELATION)))
    assert not classifier_shift(_passage(NoveltyProjectionCase(source_relation=BASE_RELATION, target_relation=BASE_RELATION)))


def test_philosophy_coarsening_creates_classifier_novelty_exhaustive():
    """thm:philosophy-coarsening-creates-classifier-novelty; Lean: BEDC.Meta.ClassifierIncrement.StructuralDiscovery; primitive: classifier_shift, structural_discovery."""
    pair_sets = tuple(powerset((PAIR_AB, PAIR_AC)))
    for source_pairs, target_pairs in product(pair_sets, repeat=2):
        source = _relation_for_pairs(source_pairs)
        target = _relation_for_pairs(target_pairs)
        if _strict_coarsening(source, target):
            changed_rows = frozenset({ROW_AB for pair in source_pairs ^ target_pairs if pair == PAIR_AB} | {ROW_AC for pair in source_pairs ^ target_pairs if pair == PAIR_AC})
            passage = _passage(NoveltyProjectionCase(source_relation=source, target_relation=target, surface_used=SURFACE_AB_AC, ledger_policy=changed_rows, passage_rows=changed_rows))
            assert classifier_shift(passage)
    assert structural_discovery(_passage(NoveltyProjectionCase(source_relation=REFINED_RELATION, target_relation=BASE_RELATION)))
    assert not classifier_shift(_passage(NoveltyProjectionCase(source_relation=BASE_RELATION, target_relation=BASE_RELATION)))


def test_philosophy_reorganization_creates_classifier_novelty_exhaustive():
    """thm:philosophy-reorganization-creates-classifier-novelty; Lean: BEDC.Meta.DiscoveryCertificate.structuralDiscovery_classifier_shift; primitive: classifier_shift, structural_discovery."""
    pair_sets = tuple(powerset((PAIR_AB, PAIR_AC)))
    for source_pairs, target_pairs in product(pair_sets, repeat=2):
        source = _relation_for_pairs(source_pairs)
        target = _relation_for_pairs(target_pairs)
        if _reorganization(source, target):
            passage = _passage(
                NoveltyProjectionCase(
                    source_relation=source,
                    target_relation=target,
                    surface_used=SURFACE_AB_AC,
                    ledger_policy=POLICY_AB_AC,
                    passage_rows=POLICY_AB_AC,
                )
            )
            assert classifier_shift(passage)
    assert structural_discovery(_passage(NoveltyProjectionCase(source_relation=BASE_RELATION, target_relation=REORGANIZED_RELATION, surface_used=SURFACE_AB_AC, ledger_policy=POLICY_AB_AC, passage_rows=POLICY_AB_AC)))
    assert not classifier_shift(_passage(NoveltyProjectionCase(source_relation=BASE_RELATION, target_relation=BASE_RELATION)))


def test_philosophy_discovery_need_not_only_refine_exhaustive():
    """cor:philosophy-discovery-need-not-only-refine; Lean: BEDC.Meta.DiscoveryCertificate.StructuralDiscovery; primitive: structural_discovery, classifier_shift."""
    modes = (
        (BASE_RELATION, REFINED_RELATION, True),
        (REFINED_RELATION, BASE_RELATION, False),
        (BASE_RELATION, REORGANIZED_RELATION, False),
    )
    for source, target, only_refine in modes:
        passage = _passage(NoveltyProjectionCase(source_relation=source, target_relation=target, surface_used=SURFACE_AB_AC, ledger_policy=POLICY_AB_AC, passage_rows=POLICY_AB_AC))
        assert structural_discovery(passage)
        assert classifier_shift(passage)
        assert _strict_refinement(source, target) == only_refine
    assert structural_discovery(_passage(NoveltyProjectionCase(source_relation=REFINED_RELATION, target_relation=BASE_RELATION)))
    assert not structural_discovery(_passage(NoveltyProjectionCase(source_relation=BASE_RELATION, target_relation=BASE_RELATION)))


def test_philosophy_certified_discovery_requires_namecert_ledger_exhaustive():
    """thm:philosophy-certified-discovery-requires-namecert-ledger; Lean: BEDC.Meta.DiscoveryCertificate.structuralDiscovery_certificate; primitive: certified_discovery, ledger_complete."""
    for certificate, rows, boundary in product((UNCERTIFIED, CERTIFIED), powerset((ROW_AB,)), (frozenset(), frozenset({"outside"}))):
        item = NoveltyProjectionCase(certificate=certificate, passage_rows=rows, claim_rows=rows, boundary=boundary)
        claim = _claim(item)
        if discovery.certified_discovery(claim):
            assert certificate["cert_status"] == "certified"
            assert ledger_complete(POLICY_AB, rows)
            assert boundary
    assert discovery.certified_discovery(_claim(NoveltyProjectionCase()))
    assert not discovery.certified_discovery(_claim(NoveltyProjectionCase(passage_rows=frozenset(), claim_rows=frozenset())))


def test_philosophy_positive_discovery_requires_novelty_net_gain_exhaustive():
    """thm:philosophy-positive-discovery-requires-novelty-net-gain; Lean: BEDC.Meta.DiscoveryCertificate.positiveDiscovery_classifier_shift; primitive: positive_discovery, positive_information."""
    for shifted, benefit in product((False, True), (0.0, 0.2, 1.0)):
        item = NoveltyProjectionCase(target_relation=REFINED_RELATION if shifted else BASE_RELATION, benefit_terms={"coverage": benefit})
        claim = _claim(item)
        if discovery.positive_discovery(claim):
            assert classifier_shift(claim.passage)
            assert discovery.positive_information(claim)
    assert discovery.positive_discovery(_claim(NoveltyProjectionCase(benefit_terms={"coverage": 1.0})))
    assert not discovery.positive_discovery(_claim(NoveltyProjectionCase(benefit_terms={"coverage": 0.0})))


def test_philosophy_discovery_candidate_not_certified_discovery_exhaustive():
    """thm:philosophy-discovery-candidate-not-certified-discovery; Lean: BEDC.Meta.ClassifierIncrement.structural_discovery_certificate; primitive: certified_discovery, structural_discovery."""
    for certificate, rows in product((UNCERTIFIED, CERTIFIED), powerset((ROW_AB,))):
        item = NoveltyProjectionCase(certificate=certificate, passage_rows=rows, claim_rows=rows)
        claim = _claim(item)
        candidate = classifier_shift(claim.passage)
        incomplete = certificate["cert_status"] != "certified" or not ledger_complete(POLICY_AB, rows)
        if candidate and incomplete:
            assert not discovery.certified_discovery(claim)
    assert classifier_shift(_claim(NoveltyProjectionCase(certificate=UNCERTIFIED)).passage)
    assert not discovery.certified_discovery(_claim(NoveltyProjectionCase(certificate=UNCERTIFIED)))
    assert discovery.certified_discovery(_claim(NoveltyProjectionCase()))


def test_philosophy_claim_demotion_preserves_audit_soundness_exhaustive():
    """thm:philosophy-claim-demotion-preserves-audit-soundness; Lean: BEDC.GroundCompiler.AnalysisPipeline.LedgerAuditFailureKind.missingLedger; primitive: certified_discovery, positive_discovery, ledger_gap."""
    for shifted, certificate, rows in product((False, True), (UNCERTIFIED, CERTIFIED), powerset((ROW_AB,))):
        item = NoveltyProjectionCase(target_relation=REFINED_RELATION if shifted else BASE_RELATION, certificate=certificate, passage_rows=rows, claim_rows=rows)
        claim = _claim(item)
        lacks_support = not classifier_shift(claim.passage) or certificate["cert_status"] != "certified" or bool(ledger_gap(POLICY_AB, rows))
        if lacks_support:
            assert not discovery.certified_discovery(claim)
            assert not discovery.positive_discovery(claim)
    assert not discovery.positive_discovery(_claim(NoveltyProjectionCase(target_relation=BASE_RELATION, benefit_terms={"audit": 2.0})))
    assert discovery.positive_discovery(_claim(NoveltyProjectionCase()))


def test_philosophy_ndna_classifier_locus_gives_interpretability_novelty_exhaustive():
    """thm:philosophy-ndna-classifier-locus-gives-interpretability-novelty; Lean: BEDC.Meta.DiscoveryCertificate.positiveDiscovery_classifier_shift; primitive: classifier_shift, ndna_positive_criterion."""
    for ndna_locus, shifted in product((False, True), repeat=2):
        item = NoveltyProjectionCase(
            target_relation=REFINED_RELATION if shifted else BASE_RELATION,
            surface_used=frozenset(),
            ndna_classifier_locus=ndna_locus,
            ndna_complete=ndna_locus,
            ndna_anchored=ndna_locus,
            ndna_namecert_compatible=ndna_locus,
            ndna_ledger_complete=ndna_locus,
            ndna_net_information=1.0 if ndna_locus else 0.0,
        )
        claim = _claim(item)
        if ndna_locus and shifted:
            assert classifier_shift(claim.passage)
            assert structural_discovery(claim.passage)
            assert classifier_surface_delta(claim.passage) == SURFACE_AB
            assert discovery.ndna_positive_criterion(claim)
    assert discovery.ndna_positive_criterion(_claim(NoveltyProjectionCase(surface_used=frozenset(), ndna_classifier_locus=True, ndna_complete=True, ndna_anchored=True, ndna_namecert_compatible=True, ndna_ledger_complete=True, ndna_net_information=1.0)))
    assert not classifier_shift(_claim(NoveltyProjectionCase(target_relation=BASE_RELATION, ndna_classifier_locus=False)).passage)


def test_philosophy_ndna_nonclassifier_change_no_novelty_exhaustive():
    """thm:philosophy-ndna-nonclassifier-change-no-novelty; Lean: BEDC.GroundCompiler.NameCertGenerated.NameCertRecognitionRelation; primitive: classifier_shift, ndna_positive_criterion."""
    for rows, ndna_complete in product(powerset((NDNA_ROW,)), (False, True)):
        claim = _claim(
            NoveltyProjectionCase(
                target_relation=REFINED_RELATION,
                surface_used=SURFACE_AB,
                passage_rows=POLICY_AB | rows,
                claim_rows=POLICY_AB | rows,
                ndna_nonclassifier_locus=True,
                ndna_complete=ndna_complete,
                ndna_anchored=ndna_complete,
                ndna_namecert_compatible=ndna_complete,
                ndna_ledger_complete=ndna_complete,
                ndna_net_information=1.0 if ndna_complete else 0.0,
            )
        )
        assert not classifier_shift(claim.passage)
        assert not discovery.ndna_positive_criterion(claim)
    assert not discovery.ndna_positive_criterion(_claim(NoveltyProjectionCase(target_relation=REFINED_RELATION, surface_used=SURFACE_AB, ndna_nonclassifier_locus=True, ndna_complete=True, ndna_anchored=True, ndna_namecert_compatible=True, ndna_ledger_complete=True, ndna_net_information=1.0)))
    assert discovery.ndna_positive_criterion(_claim(NoveltyProjectionCase(surface_used=frozenset(), ndna_classifier_locus=True, ndna_complete=True, ndna_anchored=True, ndna_namecert_compatible=True, ndna_ledger_complete=True, ndna_net_information=1.0)))


def test_philosophy_classifier_debt_reduction_no_novelty_exhaustive():
    """thm:philosophy-classifier-debt-reduction-no-novelty; Lean: BEDC.GroundCompiler.ChapterFlow.LedgerSound; primitive: ledger_debt, classifier_shift."""
    required = frozenset({ROW_AB, LEDGER_ROW})
    costs = {ROW_AB: 2.0, LEDGER_ROW: 1.0}
    for before_rows, after_rows in product(powerset(required), repeat=2):
        if ledger_debt(ledger_gap(required, after_rows), costs) <= ledger_debt(ledger_gap(required, before_rows), costs):
            passage = _passage(NoveltyProjectionCase(target_relation=BASE_RELATION, ledger_policy=required, passage_rows=after_rows))
            assert not classifier_shift(passage)
    assert ledger_debt(ledger_gap(required, required), costs) == 0.0
    assert classifier_shift(_passage(NoveltyProjectionCase(target_relation=REFINED_RELATION, ledger_policy=POLICY_AB, passage_rows=POLICY_AB)))


def test_philosophy_critical_classifier_debt_can_force_novelty_exhaustive():
    """thm:philosophy-critical-classifier-debt-can-force-novelty; Lean: BEDC.Meta.DiscoveryCertificate.classifierNonEquivalent_not_equivalentOn; primitive: critical_gap, critical_hardening_gap, classifier_shift."""
    backend = HardeningBackend("lean", frozenset({ROW_AB}))
    critical_entry = LedgerEntry(ROW_AB, "classifier-boundary", critical=True)
    for repair_forces_boundary, hardened in product((False, True), repeat=2):
        target = REFINED_RELATION if repair_forces_boundary else BASE_RELATION
        profile = HardeningProfile(CERTIFIED, frozenset(), frozenset(), frozenset(), POLICY_AB, POLICY_AB, POLICY_AB, POLICY_AB if hardened else frozenset(), frozenset(), frozenset())
        passage = _passage(NoveltyProjectionCase(target_relation=target, ledger_policy=POLICY_AB, passage_rows=POLICY_AB))
        assert critical_gap((critical_entry,)) == frozenset({ROW_AB})
        if repair_forces_boundary:
            assert classifier_shift(passage)
        if hardened:
            assert not critical_hardening_gap(profile, backend)
    assert classifier_shift(_passage(NoveltyProjectionCase(target_relation=REFINED_RELATION)))
    assert not classifier_shift(_passage(NoveltyProjectionCase(target_relation=BASE_RELATION)))


def test_philosophy_verification_only_hardening_no_classifier_novelty_exhaustive():
    """thm:philosophy-verification-only-hardening-no-classifier-novelty; Lean: BEDC.GroundCompiler.SelfHostingCompilerFlow.GlobalVerificationSoundness; primitive: fully_hardened_classifier, classifier_shift."""
    backend = HardeningBackend("lean", frozenset({VERIFY_ROW}))
    for hardened, recorded in product((False, True), repeat=2):
        profile = _hardening_profile(hardened=hardened, recorded=recorded)
        passage = _passage(NoveltyProjectionCase(target_relation=BASE_RELATION, hardening_profile=profile, hardening_backend=backend))
        assert not classifier_shift(passage)
        if hardened and recorded:
            assert fully_hardened_classifier(profile, backend)
    assert fully_hardened_classifier(_hardening_profile(hardened=True, recorded=True), backend)
    assert classifier_shift(_passage(NoveltyProjectionCase(target_relation=REFINED_RELATION, hardening_profile=_hardening_profile(), hardening_backend=backend)))


def test_philosophy_formal_classifier_discovery_requires_witness_exhaustive():
    """thm:philosophy-formal-classifier-discovery-requires-witness; Lean: BEDC.Meta.DiscoveryCertificate.structuralDiscovery_classifier_shift; primitive: certified_discovery, classifier_shift."""
    for witness, shifted in product((False, True), repeat=2):
        item = NoveltyProjectionCase(target_relation=REFINED_RELATION if shifted else BASE_RELATION, local_or_formal_witness=witness)
        claim = _claim(item)
        if discovery.certified_discovery(claim):
            assert witness
            assert classifier_shift(claim.passage)
    assert discovery.certified_discovery(_claim(NoveltyProjectionCase(local_or_formal_witness=True)))
    assert not discovery.certified_discovery(_claim(NoveltyProjectionCase(local_or_formal_witness=False)))


def test_philosophy_interpretability_classifier_novelty_theorem_exhaustive():
    """thm:philosophy-interpretability-classifier-novelty-theorem; Lean: BEDC.Meta.DiscoveryCertificate.positiveDiscovery_classifier_shift; primitive: capstone_positive_interpretability_discovery, structural_discovery."""
    for shifted, certificate, rows, benefit in product((False, True), (UNCERTIFIED, CERTIFIED), powerset((ROW_AB,)), (0.0, 1.0)):
        item = NoveltyProjectionCase(
            target_relation=REFINED_RELATION if shifted else BASE_RELATION,
            certificate=certificate,
            passage_rows=rows,
            claim_rows=rows,
            benefit_terms={"coverage": benefit},
        )
        claim = _claim(item)
        assert discovery.capstone_positive_interpretability_discovery(claim) == (
            discovery.positive_discovery(claim)
            and discovery.certified_discovery(claim)
            and classifier_shift(claim.passage)
            and discovery.ledger_completion(claim)
            and discovery.protocol_complete(claim)
            and discovery.protocol_scope_complete(claim)
            and discovery.debt_complete(claim)
            and discovery.net_information(claim) > 0.0
        )
    assert discovery.capstone_positive_interpretability_discovery(_claim(NoveltyProjectionCase(benefit_terms={"coverage": 1.0})))
    assert not discovery.capstone_positive_interpretability_discovery(_claim(NoveltyProjectionCase(target_relation=BASE_RELATION, benefit_terms={"feature-accumulation": 2.0})))
