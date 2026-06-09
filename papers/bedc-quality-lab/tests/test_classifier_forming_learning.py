from itertools import combinations, product

from bedc_quality_lab import discovery
from bedc_quality_lab.classifier_shift import ClassifierPassage, ClassifierState, classifier_shift, shift_information, structural_discovery
from bedc_quality_lab.hardening import HardeningBackend, HardeningProfile, critical_hardening_gap, fully_hardened_classifier
from bedc_quality_lab.ledger import LedgerRowKey, ledger_complete, ledger_debt, ledger_gap
from bedc_quality_lab.metrics import classifier_certificate
from bedc_quality_lab.scope import GlobalResolutionClaim, Scope, ScopedCertificate, global_ledger_complete, global_required_rows, scope_rows, scoped_resolved


LEARNING_SOURCE_ROW = LedgerRowKey("source", "learning-trace")
PATTERN_ROW = LedgerRowKey("pattern", "learned-structure")
CLASSIFIER_ROW = LedgerRowKey("classifier", "learned-classifier")
STABILITY_ROW = LedgerRowKey("stability", "transfer-witness")
LEARNING_LEDGER_ROW = LedgerRowKey("ledger", "learning-residue")
TENSOR_ROW = LedgerRowKey("tensor-namecert", "activation-distinction")
TRANSFER_ROW = LedgerRowKey("transfer", "target-boundary")
SHORTCUT_ROW = LedgerRowKey("shortcut", "spurious-correlation")
COMPRESSION_ROW = LedgerRowKey("compression", "collapsed-distinction")
VERIFICATION_ROW = LedgerRowKey("verification", "learning-claim")
BACKEND_ROW = LedgerRowKey("verification", "proof-backend")
SHIFT_ROW = LedgerRowKey("classifier", "u->v")
NAMECERT_ROWS = frozenset({LEARNING_SOURCE_ROW, PATTERN_ROW, CLASSIFIER_ROW, STABILITY_ROW, LEARNING_LEDGER_ROW})
POLICY = frozenset({SHIFT_ROW})
SOURCE_IDS = frozenset({"u", "v"})
PAIR = ("u", "v")
BASE_RELATION = frozenset({("u", "u", "same"), ("u", "v", "near"), ("v", "v", "same")})
SHIFTED_RELATION = frozenset({("u", "u", "same"), ("u", "v", "far"), ("v", "v", "same")})
CERTIFIED = classifier_certificate({"linear_identifiability_r2": 0.95, "approx_identifiability_proxy": 0.90})
UNCERTIFIED = classifier_certificate({"linear_identifiability_r2": 0.10, "approx_identifiability_proxy": 0.10})


class LearningCase:
    def __init__(self, **kwargs):
        defaults = dict(
            shifted=True, certificate=None, passage_rows=POLICY, claim_rows=POLICY, required_rows=POLICY,
            benefit=None, score=None, debt=None, boundary=frozenset({"outside-target"}), scope_sealed=True,
            laundering=frozenset(), omitted=None, verification_assisted=False, verification_benefit=0.0,
            verification_required=frozenset(), verification_recorded=frozenset(),
        )
        self.__dict__.update(defaults | kwargs)


def powerset(values):
    values = tuple(values)
    for size in range(len(values) + 1):
        for members in combinations(values, size):
            yield frozenset(members)


def learning_scope(behavior_id="learning"):
    return Scope(frozenset({"train", "target"}), "learner", "training-family", behavior_id)


def learning_certificate(*, required=NAMECERT_ROWS, recorded=NAMECERT_ROWS, certificate=CERTIFIED, boundary=frozenset({"outside-target"})):
    scope = learning_scope()
    return ScopedCertificate(scope, "learned-classifier", "learning-namecert", scope_rows(scope) | required, scope_rows(scope) | recorded, certificate, boundary)


def learning_state(*, shifted=False, certificate=CERTIFIED, surface=frozenset({PAIR}), record_count=0, feature_count=1):
    return ClassifierState(
        SOURCE_IDS,
        "classifier-forming-learning",
        POLICY,
        SHIFTED_RELATION if shifted else BASE_RELATION,
        certificate,
        surface,
        record_count=record_count,
        feature_count=feature_count,
    )


def learning_passage(*, shifted=True, certificate=CERTIFIED, recorded_rows=POLICY, surface=frozenset({PAIR}), record_count=0, feature_count=1):
    return ClassifierPassage(
        source=learning_state(shifted=False),
        target=learning_state(shifted=shifted, certificate=certificate, surface=surface, record_count=record_count, feature_count=feature_count),
        recorded_rows=recorded_rows,
    )


def learning_claim(item=LearningCase(), *, scoped_certificate=None, global_claim=None, hardening=None, backend=None):
    certificate = CERTIFIED if item.certificate is None else item.certificate
    scoped = learning_certificate(certificate=certificate, boundary=item.boundary) if scoped_certificate is None else scoped_certificate
    return discovery.DiscoveryClaim(
        passage=learning_passage(shifted=item.shifted, certificate=certificate, recorded_rows=item.passage_rows),
        benefit_terms={"coverage": 1.0} if item.benefit is None else item.benefit,
        score_terms={"training": 0.10} if item.score is None else item.score,
        debt_terms={"ledger": 0.10} if item.debt is None else item.debt,
        ledger_required_rows=item.required_rows,
        ledger_recorded_rows=item.claim_rows,
        public_cost_protocol=True,
        scope_sealed=item.scope_sealed,
        not_claimed_boundary=item.boundary,
        benefit_modes=frozenset({"coverage", "transfer"}),
        omitted_debt_terms={} if item.omitted is None else item.omitted,
        scoped_certificate=scoped,
        global_claim=global_claim,
        hardening_profile=hardening,
        hardening_backend=backend,
        verification_assisted=item.verification_assisted,
        verification_benefit=item.verification_benefit,
        verification_required_rows=item.verification_required,
        verification_recorded_rows=item.verification_recorded,
        laundering_modes=item.laundering,
    )


def hardening_profile(*, recorded=frozenset({VERIFICATION_ROW, BACKEND_ROW}), hardened=frozenset({VERIFICATION_ROW, BACKEND_ROW}), frontier=frozenset()):
    rows = frozenset({VERIFICATION_ROW, BACKEND_ROW})
    return HardeningProfile(CERTIFIED, rows, rows, frozenset(), rows, recorded, rows, hardened, frontier, frozenset())


def global_learning_claim(recorded_rows=None):
    cert = learning_certificate(required=NAMECERT_ROWS | frozenset({TRANSFER_ROW}), recorded=NAMECERT_ROWS | frozenset({TRANSFER_ROW}))
    base = GlobalResolutionClaim("learner", frozenset({"learning"}), (cert,), frozenset())
    return GlobalResolutionClaim(base.model_id, base.behavior_family, base.certificates, global_required_rows(base) if recorded_rows is None else recorded_rows)


def test_parameter_motion_not_learning_discovery_exhaustive():
    """thm:philosophy-parameter-motion-not-learning-discovery; Lean: BEDC.Meta.ClassifierIncrement.StructuralDiscovery; primitive: classifier_shift, structural_discovery."""
    for moved, rows in product((False, True), powerset((SHIFT_ROW,))):
        passage = learning_passage(shifted=False, recorded_rows=rows, record_count=1 if moved else 0)
        assert not classifier_shift(passage)
        assert not structural_discovery(passage)
    assert not structural_discovery(learning_passage(shifted=False, record_count=7))
    assert structural_discovery(learning_passage(shifted=True, recorded_rows=POLICY))


def test_model_size_not_certified_information_exhaustive():
    """thm:philosophy-model-size-not-certified-information; Lean: BEDC.GroundCompiler.MetricsFlow.QualityMetricEnvelope; primitive: classifier_certificate, shift_information."""
    for features, certificate in product((1, 8, 64), (UNCERTIFIED, CERTIFIED)):
        passage = learning_passage(shifted=False, certificate=certificate, feature_count=features)
        assert shift_information(passage) == 0
    assert shift_information(learning_passage(shifted=False, feature_count=64)) == 0
    assert shift_information(learning_passage(shifted=True, feature_count=1)) == 1


def test_loss_reduction_not_learning_discovery_exhaustive():
    """thm:philosophy-loss-reduction-not-learning-discovery; Lean: BEDC.GroundCompiler.MetricsFlow.MetricCertificateFlow; primitive: structural_discovery, positive_discovery."""
    for loss_delta, shifted in product((-1.0, -0.2, 0.0), (False, True)):
        claim = learning_claim(LearningCase(shifted=shifted, benefit={"loss": max(0.0, -loss_delta)}))
        if loss_delta < 0.0 and not shifted:
            assert not discovery.positive_discovery(claim)
    assert not discovery.positive_discovery(learning_claim(LearningCase(shifted=False, benefit={"loss": 1.0})))
    assert structural_discovery(learning_passage(shifted=True))


def test_learning_discovery_can_precede_loss_reduction_exhaustive():
    """thm:philosophy-learning-discovery-can-precede-loss-reduction; Lean: BEDC.Meta.DiscoveryCertificate.DiscoveryTransition; primitive: certified_discovery, discovery_becomes_positive_later."""
    for benefit in (0.0, 0.05, 0.3):
        initial = learning_claim(LearningCase(benefit={"future-transfer": benefit}, score={"training": 0.2}, debt={"ledger": 0.2}))
        assert discovery.certified_discovery(initial)
        if discovery.net_information(initial) <= 0.0:
            later = learning_claim(LearningCase(benefit={"future-transfer": 1.0}))
            assert discovery.discovery_becomes_positive_later(initial, later)
    assert discovery.certified_discovery(learning_claim(LearningCase(benefit={"future-transfer": 0.0}, score={"training": 0.2}, debt={"ledger": 0.2})))
    assert discovery.positive_discovery(learning_claim(LearningCase(benefit={"future-transfer": 1.0})))


def test_performance_gain_not_certified_explanation_exhaustive():
    """thm:philosophy-performance-gain-not-certified-explanation; Lean: BEDC.GroundCompiler.MetricsFlow.MetricClaimKind.positiveReuseDepthImpliesReuseCertificate; primitive: positive_information, positive_discovery."""
    for gain, shifted in product((0.0, 0.5, 1.5), (False, True)):
        claim = learning_claim(LearningCase(shifted=shifted, benefit={"benchmark": gain}))
        if discovery.positive_information(claim) and not shifted:
            assert not discovery.positive_discovery(claim)
    assert discovery.positive_information(learning_claim(LearningCase(shifted=False, benefit={"benchmark": 1.5})))
    assert discovery.positive_discovery(learning_claim(LearningCase(shifted=True, benefit={"benchmark": 1.5})))


def test_training_success_not_structural_learning_exhaustive():
    """cor:philosophy-training-success-not-structural-learning; Lean: BEDC.GroundCompiler.AnalysisPipeline.StageLedgerAudit; primitive: classifier_shift, positive_discovery."""
    for metric_success, rows in product((False, True), powerset((SHIFT_ROW,))):
        claim = learning_claim(LearningCase(shifted=False, passage_rows=rows, claim_rows=rows, benefit={"metric": 1.0 if metric_success else 0.0}))
        assert not classifier_shift(claim.passage)
        assert not discovery.positive_discovery(claim)
    assert not discovery.positive_discovery(learning_claim(LearningCase(shifted=False, benefit={"metric": 2.0})))
    assert discovery.positive_discovery(learning_claim(LearningCase(shifted=True, benefit={"metric": 2.0})))


def test_memorization_not_structural_learning_exhaustive():
    """thm:philosophy-memorization-not-structural-learning; Lean: BEDC.Meta.DiscoveryCertificate.NameCertFiveRows; primitive: structural_discovery, classifier_shift."""
    for records, shifted in product((0, 1, 5), (False, True)):
        passage = learning_passage(shifted=shifted, surface=frozenset() if records else frozenset({PAIR}), record_count=records)
        if records and not passage.target.surface_used:
            assert not structural_discovery(passage)
    assert not structural_discovery(learning_passage(shifted=True, surface=frozenset(), record_count=5))
    assert structural_discovery(learning_passage(shifted=True, surface=frozenset({PAIR}), record_count=0))


def test_certified_generalization_structural_learning_exhaustive():
    """thm:philosophy-certified-generalization-structural-learning; Lean: BEDC.Reflection.compilerPreservesClassifiers; primitive: scoped_resolved, structural_discovery, positive_discovery."""
    required = NAMECERT_ROWS | frozenset({TRANSFER_ROW})
    for rows in powerset(required):
        cert = learning_certificate(required=required, recorded=rows)
        if scoped_resolved(cert):
            assert structural_discovery(learning_passage())
    positive_cert = learning_certificate(required=required, recorded=required)
    gap_cert = learning_certificate(required=required, recorded=required - {TRANSFER_ROW})
    assert scoped_resolved(positive_cert) and discovery.positive_discovery(learning_claim(scoped_certificate=positive_cert))
    assert not scoped_resolved(gap_cert)


def test_learning_namecert_certified_object_exhaustive():
    """thm:philosophy-learning-namecert-certified-object; Lean: BEDC.Meta.DiscoveryCertificate.nameCertFiveRows_ledger; primitive: ledger_complete, scoped_resolved."""
    for rows in powerset(NAMECERT_ROWS):
        cert = learning_certificate(recorded=rows)
        assert scoped_resolved(cert) == ledger_complete(NAMECERT_ROWS, rows)
    assert scoped_resolved(learning_certificate(recorded=NAMECERT_ROWS))
    assert not scoped_resolved(learning_certificate(recorded=NAMECERT_ROWS - {LEARNING_LEDGER_ROW}))


def test_learning_claims_require_ledger_exhaustive():
    """thm:philosophy-learning-claims-require-ledger; Lean: BEDC.GroundCompiler.ChapterFlow.LedgerSound; primitive: ledger_gap, ledger_complete, positive_discovery."""
    for rows in powerset(POLICY):
        claim = learning_claim(LearningCase(passage_rows=rows, claim_rows=rows))
        assert discovery.ledger_completion(claim) == ledger_complete(POLICY, rows)
        if ledger_gap(POLICY, rows):
            assert not discovery.positive_discovery(claim)
    assert not discovery.positive_discovery(learning_claim(LearningCase(passage_rows=frozenset(), claim_rows=frozenset())))
    assert discovery.positive_discovery(learning_claim())


def test_shortcut_learning_not_certified_without_ledger_exhaustive():
    """thm:philosophy-shortcut-learning-not-certified-without-ledger; Lean: BEDC.GroundCompiler.AnalysisPipeline.LedgerAuditFailureKind.motifWithoutLedger; primitive: laundering_invalidates, ledger_gap."""
    required = POLICY | frozenset({SHORTCUT_ROW})
    for rows in powerset(required):
        claim = learning_claim(LearningCase(required_rows=required, claim_rows=rows, laundering=frozenset({"shortcut"})))
        assert discovery.laundering_invalidates(claim)
        if SHORTCUT_ROW not in rows:
            assert ledger_gap(required, rows)
    assert discovery.laundering_invalidates(learning_claim(LearningCase(required_rows=required, claim_rows=POLICY, laundering=frozenset({"shortcut"}))))
    assert discovery.positive_discovery(learning_claim(LearningCase(required_rows=required, claim_rows=required)))


def test_representation_learning_requires_tensor_namecert_exhaustive():
    """thm:philosophy-representation-learning-requires-tensor-namecert; Lean: BEDC.GroundCompiler.NameCertGenerated.CompleteFiveFieldRecognition; primitive: ledger_complete, scoped_resolved."""
    required = NAMECERT_ROWS | frozenset({TENSOR_ROW})
    for rows in powerset(required):
        cert = learning_certificate(required=required, recorded=rows)
        assert scoped_resolved(cert) == ledger_complete(required, rows)
    assert not scoped_resolved(learning_certificate(required=required, recorded=required - {TENSOR_ROW}))
    assert scoped_resolved(learning_certificate(required=required, recorded=required))


def test_representation_compression_requires_ledger_exhaustive():
    """thm:philosophy-representation-compression-requires-ledger; Lean: BEDC.GroundCompiler.SemanticMotif.LedgerCompressionMotif; primitive: ledger_gap, ledger_debt."""
    required = frozenset({COMPRESSION_ROW, LEARNING_LEDGER_ROW})
    costs = {COMPRESSION_ROW: 2.0, LEARNING_LEDGER_ROW: 1.0}
    for rows in powerset(required):
        gap = ledger_gap(required, rows)
        assert (ledger_debt(gap, costs) == 0.0) == ledger_complete(required, rows)
    assert ledger_debt(ledger_gap(required, frozenset({LEARNING_LEDGER_ROW})), costs) > 0.0
    assert ledger_debt(ledger_gap(required, required), costs) == 0.0


def test_certified_generalizing_learner_transfer_ledger_exhaustive():
    """thm:philosophy-certified-generalizing-learner-transfer-ledger; Lean: BEDC.Reflection.compilerClassifierBridge; primitive: global_required_rows, global_ledger_complete."""
    complete = global_learning_claim()
    required = global_required_rows(complete)
    for rows in powerset((TRANSFER_ROW,)):
        partial = global_learning_claim(recorded_rows=(required - {TRANSFER_ROW}) | rows)
        assert global_ledger_complete(partial) == (TRANSFER_ROW in rows)
    assert global_ledger_complete(complete)
    assert not global_ledger_complete(global_learning_claim(recorded_rows=required - {TRANSFER_ROW}))


def test_learning_optimization_not_structural_exhaustive():
    """thm:philosophy-learning-optimization-not-structural; Lean: BEDC.Meta.ClassifierIncrement.MechanicalComputation; primitive: classifier_shift, structural_discovery."""
    for loss_gain, performance_gain, records in product((0.0, 1.0), (0.0, 1.0), (0, 5)):
        passage = learning_passage(shifted=False, record_count=records)
        assert not classifier_shift(passage)
        assert not structural_discovery(passage)
        assert loss_gain + performance_gain + records >= 0
    assert not structural_discovery(learning_passage(shifted=False, record_count=5))
    assert structural_discovery(learning_passage(shifted=True))


def test_structural_learning_not_immediately_positive_exhaustive():
    """thm:philosophy-structural-learning-not-immediately-positive; Lean: BEDC.Meta.DiscoveryCertificate.discovery_debt_witness; primitive: certified_discovery, discovery_becomes_positive_later."""
    for cost in (0.2, 0.8, 1.4):
        initial = learning_claim(LearningCase(benefit={"coverage": 0.5}, score={"verification": cost}, debt={"ledger": 0.2}))
        assert discovery.certified_discovery(initial)
        if discovery.net_information(initial) <= 0.0:
            assert not discovery.positive_discovery(initial)
    assert not discovery.positive_discovery(learning_claim(LearningCase(benefit={"coverage": 0.5}, score={"verification": 1.4}, debt={"ledger": 0.2})))
    assert discovery.positive_discovery(learning_claim(LearningCase(benefit={"coverage": 1.4}, score={"verification": 0.2}, debt={"ledger": 0.1})))


def test_verified_learning_claim_not_learning_discovery_exhaustive():
    """thm:philosophy-verified-learning-claim-not-learning-discovery; Lean: BEDC.GroundCompiler.AnalysisPipeline.CertificateObligationDischarge; primitive: verification_assisted_positive_discovery, classifier_shift."""
    item = LearningCase(
        shifted=False,
        benefit={"verification": 1.0},
        verification_assisted=True,
        verification_benefit=1.0,
        verification_required=frozenset({VERIFICATION_ROW}),
        verification_recorded=frozenset({VERIFICATION_ROW}),
    )
    for shifted, verified in product((False, True), (False, True)):
        claim = learning_claim(
            LearningCase(
                shifted=shifted,
                benefit={"verification": 1.0},
                verification_assisted=verified,
                verification_benefit=1.0 if verified else 0.0,
                verification_required=frozenset({VERIFICATION_ROW}),
                verification_recorded=frozenset({VERIFICATION_ROW}) if verified else frozenset(),
            )
        )
        if verified and not classifier_shift(claim.passage):
            assert not discovery.verification_assisted_positive_discovery(claim)
    assert not discovery.verification_assisted_positive_discovery(learning_claim(item))
    assert discovery.verification_assisted_positive_discovery(learning_claim(LearningCase(verification_assisted=True, verification_benefit=1.0, verification_required=frozenset({VERIFICATION_ROW}), verification_recorded=frozenset({VERIFICATION_ROW}))))


def test_formal_hardening_cost_enters_learning_information_exhaustive():
    """thm:philosophy-formal-hardening-cost-enters-learning-information; Lean: BEDC.GroundCompiler.SelfHostingCompilerFlow.GlobalVerificationSoundness; primitive: verification_cost_counted, critical_hardening_gap."""
    backend = HardeningBackend("lean", frozenset({VERIFICATION_ROW, BACKEND_ROW}))
    for recorded, hardened in product(powerset((VERIFICATION_ROW, BACKEND_ROW)), repeat=2):
        profile = hardening_profile(recorded=recorded, hardened=hardened)
        claim = learning_claim(
            LearningCase(
                verification_assisted=True,
                verification_benefit=0.5,
                verification_required=frozenset({VERIFICATION_ROW, BACKEND_ROW}),
                verification_recorded=recorded,
                score={"verification": 0.2},
            ),
            hardening=profile,
            backend=backend,
        )
        assert discovery.verification_cost_counted(claim) == ledger_complete(frozenset({VERIFICATION_ROW, BACKEND_ROW}), recorded)
        if critical_hardening_gap(profile, backend):
            assert not fully_hardened_classifier(profile, backend)
    assert discovery.verification_cost_counted(learning_claim(LearningCase(verification_assisted=True, verification_benefit=0.5, verification_required=frozenset({VERIFICATION_ROW}), verification_recorded=frozenset({VERIFICATION_ROW}), score={"verification": 0.2})))
    assert not discovery.verification_cost_counted(learning_claim(LearningCase(verification_assisted=True, verification_benefit=0.5, verification_required=frozenset({VERIFICATION_ROW}), verification_recorded=frozenset(), score={"verification": 0.2})))


def test_learning_laundering_invalidates_discovery_exhaustive():
    """thm:philosophy-learning-laundering-invalidates-discovery; Lean: BEDC.GroundCompiler.AnalysisPipeline.LedgerAuditFailureKind.missingLedger; primitive: laundering_invalidates, positive_discovery."""
    modes = ("loss", "benchmark", "parameter", "memorization", "shortcut")
    for active in powerset(modes):
        claim = learning_claim(LearningCase(laundering=active))
        assert discovery.laundering_invalidates(claim) == bool(active)
        if active:
            assert not discovery.positive_discovery(claim)
    assert discovery.laundering_invalidates(learning_claim(LearningCase(laundering=frozenset({"loss"}))))
    assert discovery.positive_discovery(learning_claim(LearningCase(laundering=frozenset())))


def test_classifier_forming_learning_theorem_exhaustive():
    """thm:philosophy-classifier-forming-learning-theorem; Lean: BEDC.Meta.DiscoveryCertificate.discovery_transition_witness; primitive: capstone_positive_interpretability_discovery."""
    for shifted, rows, boundary, laundering in product((False, True), powerset((SHIFT_ROW,)), (frozenset(), frozenset({"outside-target"})), (frozenset(), frozenset({"loss"}))):
        claim = learning_claim(LearningCase(shifted=shifted, passage_rows=rows, claim_rows=rows, boundary=boundary, laundering=laundering))
        expected = (
            discovery.positive_discovery(claim)
            and discovery.certified_discovery(claim)
            and classifier_shift(claim.passage)
            and discovery.ledger_completion(claim)
            and discovery.protocol_complete(claim)
            and discovery.protocol_scope_complete(claim)
            and discovery.debt_complete(claim)
            and discovery.net_information(claim) > 0.0
        )
        assert discovery.capstone_positive_interpretability_discovery(claim) == expected
    assert discovery.capstone_positive_interpretability_discovery(learning_claim())
    assert not discovery.capstone_positive_interpretability_discovery(learning_claim(LearningCase(shifted=False, benefit={"loss": 2.0})))
