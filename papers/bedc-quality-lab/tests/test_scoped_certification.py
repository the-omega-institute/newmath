from itertools import combinations, product

from bedc_quality_lab.classifier_shift import (
    ClassifierPassage,
    ClassifierState,
    classifier_surface_delta,
)
from bedc_quality_lab.ledger import LedgerRowKey
from bedc_quality_lab.scope import (
    GlobalResolutionClaim,
    Scope,
    ScopedCertificate,
    bridge_rows,
    global_required_rows,
    global_ledger_complete,
    globally_resolved,
    scope_rows,
    scoped_resolved,
    semantic_rows,
    verification_rows,
)


CERTIFIED = {"cert_status": "certified"}
UNCERTIFIED = {"cert_status": "uncertified"}
KERNEL_CHECKED = {"cert_status": "certified", "verification_status": "kernel-checked"}
PRODUCT_CERTIFIED = {"cert_status": "certified", "product_classifier": True}
SEMANTIC_CERTIFIED = {"cert_status": "certified", "semantic_globalizer": True}


def powerset(rows):
    rows = tuple(rows)
    for size in range(len(rows) + 1):
        for members in combinations(rows, size):
            yield frozenset(members)


def scope(
    behavior_id="B1",
    domain_ids=frozenset({"D0"}),
    model_id="M",
    admitted_family_id="A",
):
    return Scope(
        domain_ids=domain_ids,
        model_id=model_id,
        admitted_family_id=admitted_family_id,
        behavior_id=behavior_id,
    )


def scoped_cert(
    behavior_id="B1",
    domain_ids=frozenset({"D0"}),
    model_id="M",
    certificate=CERTIFIED,
    recorded_rows=None,
    not_claimed_boundary=frozenset({"outside-scope"}),
    classifier_id="C1",
    namecert_id="N1",
):
    cert_scope = scope(behavior_id=behavior_id, domain_ids=domain_ids, model_id=model_id)
    required = scope_rows(cert_scope)
    recorded = required if recorded_rows is None else recorded_rows
    return ScopedCertificate(
        scope=cert_scope,
        classifier_id=classifier_id,
        namecert_id=namecert_id,
        required_rows=required,
        recorded_rows=recorded,
        certificate=certificate,
        not_claimed_boundary=not_claimed_boundary,
    )


def claim_for(certificates, behavior_family=None, global_recorded_rows=frozenset()):
    family = (
        frozenset(cert.scope.behavior_id for cert in certificates)
        if behavior_family is None
        else behavior_family
    )
    return GlobalResolutionClaim(
        model_id="M",
        behavior_family=family,
        certificates=tuple(certificates),
        global_recorded_rows=global_recorded_rows,
    )


def full_claim(certificates, behavior_family=None):
    claim = claim_for(certificates, behavior_family=behavior_family)
    return claim_for(
        certificates,
        behavior_family=claim.behavior_family,
        global_recorded_rows=global_required_rows(claim),
    )


def classifier_state(relation, behavior_id):
    return ClassifierState(
        source_ids=frozenset({"x", "y"}),
        pattern_id=behavior_id,
        ledger_policy=frozenset(),
        relation=relation,
        certificate=CERTIFIED,
        surface_used=frozenset({("x", "y")}),
    )


def test_scoped_resolution_not_global_resolution_exhaustive():
    """thm:philosophy-scoped-resolution-not-global-resolution; Lean: BEDC.GroundCompiler.NameCertGenerated.LedgerCompleteNameCertFlow and BEDC.GroundCompiler.SelfHostingCompilerFlow.GlobalVerificationSoundness."""
    cert = scoped_cert()
    assert scoped_resolved(cert)

    full = full_claim((cert,), behavior_family=frozenset({"B1"}))
    rows = tuple(global_required_rows(full))
    for recorded_rows in powerset(rows):
        candidate = claim_for(
            (cert,),
            behavior_family=frozenset({"B1", "B2"}),
            global_recorded_rows=recorded_rows,
        )
        assert not globally_resolved(candidate)

    scoped_only = claim_for((cert,), behavior_family=frozenset({"B1"}), global_recorded_rows=cert.recorded_rows)
    assert not globally_resolved(scoped_only)
    assert globally_resolved(full)


def test_finite_sample_closure_not_open_domain_closure_exhaustive():
    """thm:philosophy-finite-sample-closure-not-open-domain-closure; Lean: BEDC.GroundCompiler.NameCertGenerated.NameCertLedgerSoundnessEvent and BEDC.GroundCompiler.AnalysisPipeline.StageLedgerAudit."""
    finite = scoped_cert(domain_ids=frozenset({"D0"}))
    open_domain = scoped_cert(domain_ids=frozenset({"D0", "D1"}))
    new_domain_row = LedgerRowKey("source", "M:D1")

    assert scoped_resolved(finite)
    assert new_domain_row not in finite.recorded_rows
    assert new_domain_row in open_domain.required_rows

    for recorded_rows in powerset(open_domain.required_rows):
        candidate = scoped_cert(
            domain_ids=frozenset({"D0", "D1"}),
            recorded_rows=recorded_rows,
        )
        assert scoped_resolved(candidate) == open_domain.required_rows.issubset(recorded_rows)

    missing_open_domain = scoped_cert(
        domain_ids=frozenset({"D0", "D1"}),
        recorded_rows=finite.recorded_rows,
    )
    assert not scoped_resolved(missing_open_domain)
    assert scoped_resolved(open_domain)


def test_global_resolution_requires_global_ledger_exhaustive():
    """thm:philosophy-global-resolution-requires-global-ledger-principle; Lean: BEDC.GroundCompiler.SelfHostingCompilerFlow.GlobalVerificationFlow and BEDC.GroundCompiler.SelfHostingCompilerFlow.GlobalStatusCertificateFlow."""
    certs = (
        scoped_cert(behavior_id="B1", classifier_id="C1", namecert_id="N1"),
        scoped_cert(behavior_id="B2", classifier_id="C2", namecert_id="N2"),
    )
    assert all(scoped_resolved(cert) for cert in certs)
    claim = full_claim(certs)
    required = global_required_rows(claim)

    for recorded_rows in powerset(required):
        candidate = claim_for(certs, behavior_family=frozenset({"B1", "B2"}), global_recorded_rows=recorded_rows)
        assert globally_resolved(candidate) == required.issubset(recorded_rows)

    missing_one = claim_for(certs, global_recorded_rows=frozenset(tuple(required)[1:]))
    assert not globally_resolved(missing_one)
    assert globally_resolved(claim)


def test_global_resolution_requires_same_model_certificate():
    """thm:philosophy-global-resolution-requires-same-model-state; Lean: BEDC.GroundCompiler.SelfHostingCompilerFlow.GlobalVerificationFlow."""
    same_model = scoped_cert(model_id="M")
    same_model_claim = full_claim((same_model,), behavior_family=frozenset({"B1"}))
    assert globally_resolved(same_model_claim)

    cross_model = scoped_cert(model_id="N")
    cross_model_claim = full_claim((cross_model,), behavior_family=frozenset({"B1"}))
    assert cross_model_claim.model_id == "M"
    assert cross_model.scope.model_id == "N"
    assert global_ledger_complete(cross_model_claim)
    assert scoped_resolved(cross_model)
    assert not globally_resolved(cross_model_claim)


def test_no_uncertified_global_black_box_eliminator_exhaustive():
    """thm:philosophy-no-uncertified-global-black-box-eliminator; Lean: BEDC.GroundCompiler.AnalysisPipeline.AnalysisFailureKind.uncertifiedRecognizer and BEDC.GroundCompiler.NameCertGenerated.namecert_without_ledger_not_admissible."""
    cert = scoped_cert(certificate=KERNEL_CHECKED)
    claim = full_claim((cert,))
    required = global_required_rows(claim)
    row_groups = (
        {row for row in required if row.kind == "behavior-family"},
        {row for row in required if row.kind == "classifier-family"},
        {row for row in required if row.kind == "namecert-family"},
        {row for row in required if row.kind == "global-ledger"},
        verification_rows(cert),
        {row for row in required if row.kind == "not-claimed"},
    )

    for mask in product((False, True), repeat=len(row_groups)):
        recorded_rows = set(required)
        for include, rows in zip(mask, row_groups):
            if not include:
                recorded_rows.difference_update(rows)
        candidate = claim_for((cert,), global_recorded_rows=frozenset(recorded_rows))
        assert globally_resolved(candidate) == all(mask)

    uncertified = scoped_cert(certificate=UNCERTIFIED)
    uncertified_claim = claim_for(
        (uncertified,),
        global_recorded_rows=global_required_rows(claim_for((uncertified,))),
    )
    assert not globally_resolved(uncertified_claim)
    assert globally_resolved(claim)


def test_single_classifier_not_many_behaviors_exhaustive():
    """thm:philosophy-single-classifier-not-many-behaviors; Lean: BEDC.GroundCompiler.NameCertGenerated.NameCertClassifierSoundnessEvent and BEDC.GroundCompiler.AnalysisPipeline.BridgeObligationKind.normalAddressWithoutClassifierExactness."""
    relation_b1 = frozenset({("x", "x", "same"), ("x", "y", "near"), ("y", "y", "same")})
    relation_b2 = frozenset({("x", "x", "same"), ("x", "y", "far"), ("y", "y", "same")})
    passage = ClassifierPassage(
        source=classifier_state(relation_b1, "B1"),
        target=classifier_state(relation_b2, "B2"),
    )
    assert classifier_surface_delta(passage) == frozenset({("x", "y")})

    b1 = scoped_cert(behavior_id="B1", classifier_id="C1", namecert_id="N1")
    b2 = scoped_cert(behavior_id="B2", classifier_id="C2", namecert_id="N2")
    b2_rows = set(scope_rows(b2.scope))
    rows_under_test = tuple(scope_rows(b1.scope) | frozenset(b2_rows))

    for recorded_rows in powerset(rows_under_test):
        candidate_b2 = scoped_cert(
            behavior_id="B2",
            classifier_id="C2",
            namecert_id="N2",
            recorded_rows=recorded_rows,
        )
        expected_b2 = b2.required_rows.issubset(recorded_rows)
        assert scoped_resolved(candidate_b2) == expected_b2

    b1_only_claim = full_claim((b1,), behavior_family=frozenset({"B1", "B2"}))
    assert not globally_resolved(b1_only_claim)
    assert globally_resolved(full_claim((b1, b2), behavior_family=frozenset({"B1", "B2"})))


def test_product_classifiers_require_bridge_ledgers_exhaustive():
    """thm:philosophy-product-classifiers-require-bridge-ledgers; Lean: BEDC.GroundCompiler.AnalysisPipeline.LedgerAuditFailureKind.bridgeWithoutNoHostLeakLedger and BEDC.GroundCompiler.HigherCaseStudies.BridgeCertificateSupport."""
    cert = scoped_cert(certificate=PRODUCT_CERTIFIED, classifier_id="C-product")
    claim = full_claim((cert,))
    bridge = bridge_rows(cert)
    assert len(bridge) == 5

    for recorded_bridge in powerset(bridge):
        recorded_rows = global_required_rows(claim) - bridge | recorded_bridge
        candidate = claim_for((cert,), global_recorded_rows=recorded_rows)
        assert globally_resolved(candidate) == (recorded_bridge == bridge)

    no_bridge = claim_for((cert,), global_recorded_rows=global_required_rows(claim) - bridge)
    assert not global_ledger_complete(no_bridge)
    assert globally_resolved(claim)


def test_semantic_globalization_requires_semantic_ledger_exhaustive():
    """thm:philosophy-semantic-globalization-requires-semantic-ledger; Lean: BEDC.GroundCompiler.SemanticMotif.MotifLedger and BEDC.GroundCompiler.SemanticMotif.LedgerCompressionMotif."""
    cert = scoped_cert(certificate=SEMANTIC_CERTIFIED)
    claim = full_claim((cert,))
    semantic = semantic_rows(cert)
    assert len(semantic) == 9

    for recorded_semantic in powerset(semantic):
        recorded_rows = global_required_rows(claim) - semantic | recorded_semantic
        candidate = claim_for((cert,), global_recorded_rows=recorded_rows)
        assert globally_resolved(candidate) == (recorded_semantic == semantic)

    semantic_gap = claim_for((cert,), global_recorded_rows=global_required_rows(claim) - semantic)
    assert not global_ledger_complete(semantic_gap)
    assert globally_resolved(claim)


def test_scoped_proof_not_global_explanation_exhaustive():
    """thm:philosophy-scoped-proof-not-global-explanation; Lean: BEDC.GroundCompiler.SelfHostingCompilerFlow.sound_global_verification_status and BEDC.GroundCompiler.AnalysisPipeline.CertificateObligationDischarge."""
    cert = scoped_cert(certificate=KERNEL_CHECKED)
    claim = full_claim((cert,))
    verification = verification_rows(cert)
    behavior_union = {row for row in global_required_rows(claim) if row.kind == "behavior-family"}
    assert len(verification) == 8

    for recorded_verification, recorded_behavior in product(
        powerset(verification),
        powerset(behavior_union),
    ):
        recorded_rows = (
            global_required_rows(claim)
            - verification
            - behavior_union
            | recorded_verification
            | recorded_behavior
        )
        candidate = claim_for((cert,), global_recorded_rows=recorded_rows)
        assert globally_resolved(candidate) == (
            recorded_verification == verification and recorded_behavior == behavior_union
        )

    scoped_statement_only = claim_for(
        (cert,),
        global_recorded_rows=cert.recorded_rows | verification,
    )
    assert not globally_resolved(scoped_statement_only)
    assert globally_resolved(claim)
