from itertools import combinations, product

from bedc_quality_lab.hardening import (
    HardeningBackend,
    HardeningProfile,
    backend_relative_hardenable,
    critical_hardening_gap,
    fully_hardened_classifier,
    hardened,
    hardened_implies_hardenable,
    hardening_frontier,
    ledger_only_classifier,
    local_hardening_delta,
    mode_complete,
    mode_gap,
    partially_hardened_classifier,
    should_harden_immediately,
)
from bedc_quality_lab.ledger import LedgerRowKey, ledger_complete
from bedc_quality_lab.metrics import classifier_certificate
from bedc_quality_lab.scope import (
    GlobalResolutionClaim,
    Scope,
    ScopedCertificate,
    global_required_rows,
    scope_rows,
    verification_rows,
)


SOURCE = LedgerRowKey("source", "M:D0")
CLASSIFIER = LedgerRowKey("classifier", "x->y")
STABILITY = LedgerRowKey("stability", "fixed-seed")
LEDGER = LedgerRowKey("ledger", "boundary")
VERIFICATION = LedgerRowKey("verification", "M:B1:checked-statement")
SEMANTIC = LedgerRowKey("semantic", "label-boundary")
UNIVERSE = (SOURCE, CLASSIFIER, STABILITY, LEDGER, VERIFICATION, SEMANTIC)
CERTIFIED = classifier_certificate(
    {
        "linear_identifiability_r2": 0.95,
        "approx_identifiability_proxy": 0.90,
    },
)
UNCERTIFIED = classifier_certificate(
    {
        "linear_identifiability_r2": 0.10,
        "approx_identifiability_proxy": 0.10,
    },
)


def powerset(rows):
    rows = tuple(rows)
    for size in range(len(rows) + 1):
        for members in combinations(rows, size):
            yield frozenset(members)


def cert_rows():
    cert_scope = Scope(
        domain_ids=frozenset({"D0"}),
        model_id="M",
        admitted_family_id="A",
        behavior_id="B1",
    )
    certificate = ScopedCertificate(
        scope=cert_scope,
        classifier_id="C1",
        namecert_id="N1",
        required_rows=scope_rows(cert_scope),
        recorded_rows=scope_rows(cert_scope),
        certificate={**CERTIFIED, "verification_status": "kernel-checked"},
        not_claimed_boundary=frozenset({"outside-scope"}),
    )
    claim = GlobalResolutionClaim(
        model_id="M",
        behavior_family=frozenset({"B1"}),
        certificates=(certificate,),
        global_recorded_rows=frozenset(),
    )
    return scope_rows(cert_scope) | verification_rows(certificate) | global_required_rows(claim)


def profile(
    *,
    certificate=CERTIFIED,
    mode_rows=frozenset({SOURCE, CLASSIFIER, STABILITY, LEDGER}),
    declared_mode_rows=frozenset({SOURCE, CLASSIFIER, STABILITY, LEDGER}),
    open_mode_rows=frozenset(),
    ledger_required_rows=frozenset({SOURCE, CLASSIFIER, STABILITY, LEDGER}),
    ledger_recorded_rows=frozenset({SOURCE, CLASSIFIER, STABILITY, LEDGER}),
    critical_rows=frozenset({SOURCE, CLASSIFIER}),
    hardened_rows=frozenset(),
    frontier_rows=frozenset(),
    non_hardenable_residue=frozenset(),
    empirical_stability=False,
):
    return HardeningProfile(
        certificate=certificate,
        mode_rows=mode_rows,
        declared_mode_rows=declared_mode_rows,
        open_mode_rows=open_mode_rows,
        ledger_required_rows=ledger_required_rows,
        ledger_recorded_rows=ledger_recorded_rows,
        critical_rows=critical_rows,
        hardened_rows=hardened_rows,
        frontier_rows=frontier_rows,
        non_hardenable_residue=non_hardenable_residue,
        empirical_stability=empirical_stability,
    )


def test_mode_gaps_prevent_full_auditability_exhaustive():
    """thm:philosophy-mode-gaps-prevent-full-auditability; Lean: BEDC.GroundCompiler.NameCertGenerated.CompleteFiveFieldRecognition and BEDC.GroundCompiler.AnalysisPipeline.StageLedgerAudit."""
    for declared, open_rows in product(powerset(UNIVERSE[:4]), powerset(UNIVERSE[:4])):
        candidate = profile(declared_mode_rows=declared, open_mode_rows=open_rows)
        expected_gap = (frozenset(UNIVERSE[:4]) - (declared - open_rows)) | open_rows
        assert mode_gap(candidate) == expected_gap
        assert mode_complete(candidate) == (expected_gap == frozenset())

    assert mode_complete(profile())
    assert not mode_complete(profile(open_mode_rows=frozenset({SOURCE})))
    assert not mode_complete(profile(declared_mode_rows=frozenset({CLASSIFIER, STABILITY, LEDGER})))


def test_hardened_implies_hardenable_exhaustive():
    """thm:philosophy-hardened-implies-hardenable; Lean: BEDC.GroundCompiler.AnalysisPipeline.CertificateObligationDischarge and BEDC.GroundCompiler.ImplementationInterface.CertificateLeanTargetSet."""
    for hardenable_rows, hardened_rows in product(powerset(UNIVERSE[:4]), powerset(UNIVERSE[:4])):
        backend = HardeningBackend("lean", hardenable_rows)
        candidate = profile(hardened_rows=hardened_rows)

        assert hardened_implies_hardenable(candidate, backend) == hardened_rows.issubset(hardenable_rows)

    backend = HardeningBackend("lean", frozenset({SOURCE, CLASSIFIER}))
    assert hardened_implies_hardenable(profile(hardened_rows=frozenset({SOURCE})), backend)
    assert not hardened_implies_hardenable(profile(hardened_rows=frozenset({SEMANTIC})), backend)


def test_hardened_membership_exhaustive():
    for hardened_rows in powerset(UNIVERSE[:4]):
        candidate = profile(hardened_rows=hardened_rows)
        for row in UNIVERSE:
            assert hardened(candidate, row) == (row in hardened_rows)

    candidate = profile(hardened_rows=frozenset({SOURCE, CLASSIFIER}))
    assert hardened(candidate, SOURCE)
    assert not hardened(candidate, SEMANTIC)


def test_hardenability_backend_relative_exhaustive():
    """thm:philosophy-hardenability-backend-relative; Lean: BEDC.GroundCompiler.ImplementationInterface.ImplementationLeanTarget and BEDC.GroundCompiler.SelfHostingCompilerFlow.GlobalVerificationSoundness."""
    lean_backend = HardeningBackend("lean", frozenset({SOURCE, CLASSIFIER, VERIFICATION}))
    audit_backend = HardeningBackend("audit", frozenset({SOURCE, LEDGER, STABILITY}))

    found_relative_difference = False
    for row in UNIVERSE:
        lean_status = backend_relative_hardenable(lean_backend, row)
        audit_status = backend_relative_hardenable(audit_backend, row)
        if lean_status != audit_status:
            found_relative_difference = True
        assert lean_status == (row in lean_backend.hardenable_rows)
        assert audit_status == (row in audit_backend.hardenable_rows)

    assert found_relative_difference
    assert backend_relative_hardenable(lean_backend, CLASSIFIER)
    assert not backend_relative_hardenable(audit_backend, CLASSIFIER)


def test_fully_hardened_no_critical_gap_exhaustive():
    """thm:philosophy-fully-hardened-no-critical-gap; Lean: BEDC.GroundCompiler.NameCertGenerated.NameCertLedgerSoundnessEvent and BEDC.GroundCompiler.AnalysisPipeline.LedgerAuditFailureKind.missingLedger."""
    backend = HardeningBackend("lean", frozenset({SOURCE, CLASSIFIER, VERIFICATION}))
    critical_rows = frozenset({SOURCE, CLASSIFIER})

    for hardened_rows, frontier_rows, ledger_recorded_rows in product(
        powerset(critical_rows),
        powerset(critical_rows),
        powerset(critical_rows),
    ):
        candidate = profile(
            ledger_required_rows=critical_rows,
            ledger_recorded_rows=ledger_recorded_rows,
            critical_rows=critical_rows,
            hardened_rows=hardened_rows,
            frontier_rows=frontier_rows,
        )
        expected_gap = critical_rows - (hardened_rows | frontier_rows | ledger_recorded_rows)
        expected_full = (
            ledger_complete(critical_rows, ledger_recorded_rows)
            and expected_gap == frozenset()
        )

        assert critical_hardening_gap(candidate, backend) == expected_gap
        assert fully_hardened_classifier(candidate, backend) == expected_full

    full = profile(
        ledger_required_rows=critical_rows,
        ledger_recorded_rows=critical_rows,
        critical_rows=critical_rows,
        hardened_rows=critical_rows,
    )
    gap = profile(
        ledger_required_rows=critical_rows,
        ledger_recorded_rows=frozenset({SOURCE}),
        critical_rows=critical_rows,
        hardened_rows=frozenset({SOURCE}),
    )
    assert fully_hardened_classifier(full, backend)
    assert not critical_hardening_gap(full, backend)
    assert critical_hardening_gap(gap, backend) == frozenset({CLASSIFIER})
    assert not fully_hardened_classifier(gap, backend)


def test_ledger_only_classifiers_certified_exhaustive():
    """thm:philosophy-ledger-only-classifiers-certified; Lean: BEDC.GroundCompiler.NameCertGenerated.LedgerCompleteNameCertFlow and BEDC.GroundCompiler.NameCertGenerated.certified_derived_carry_ledger."""
    rows = tuple(sorted(cert_rows()))[:5]
    residue = frozenset({rows[0]})
    for certificate, recorded_rows, hardened_rows, open_rows in product(
        (CERTIFIED, UNCERTIFIED),
        powerset(rows),
        powerset((rows[1],)),
        (frozenset(), frozenset({rows[2]})),
    ):
        required = frozenset(rows)
        candidate = profile(
            certificate=certificate,
            mode_rows=required,
            declared_mode_rows=required,
            open_mode_rows=open_rows,
            ledger_required_rows=required,
            ledger_recorded_rows=recorded_rows,
            critical_rows=frozenset({rows[0], rows[1]}),
            hardened_rows=hardened_rows,
            non_hardenable_residue=residue,
        )
        expected = (
            certificate.get("cert_status") == "certified"
            and open_rows == frozenset()
            and required.issubset(recorded_rows)
            and residue.issubset(recorded_rows)
            and hardened_rows == frozenset()
        )

        assert ledger_only_classifier(candidate) == expected

    ledger_only = profile(non_hardenable_residue=frozenset({SOURCE}))
    hardened = profile(hardened_rows=frozenset({SOURCE}), non_hardenable_residue=frozenset({CLASSIFIER}))
    assert ledger_only_classifier(ledger_only)
    assert not ledger_only_classifier(hardened)


def test_partial_hardening_local_exhaustive():
    """thm:philosophy-partial-hardening-local; Lean: BEDC.GroundCompiler.AnalysisPipeline.CertificateObligationDischarge and BEDC.GroundCompiler.NameCertGenerated.NameCertClassifierSoundnessEvent."""
    critical_rows = frozenset({SOURCE, CLASSIFIER, LEDGER})
    for before_rows, after_rows in product(powerset(critical_rows), powerset(critical_rows)):
        before = profile(critical_rows=critical_rows, hardened_rows=before_rows)
        after = profile(critical_rows=critical_rows, hardened_rows=after_rows)
        expected_delta = after_rows - before_rows
        expected_partial = bool(after_rows) and bool(critical_rows - after_rows)

        assert local_hardening_delta(before, after) == expected_delta
        assert partially_hardened_classifier(after) == expected_partial

    before = profile(critical_rows=critical_rows)
    after = profile(critical_rows=critical_rows, hardened_rows=frozenset({SOURCE}))
    full = profile(critical_rows=critical_rows, hardened_rows=critical_rows)
    assert local_hardening_delta(before, after) == frozenset({SOURCE})
    assert partially_hardened_classifier(after)
    assert not partially_hardened_classifier(full)


def test_empirical_stability_not_ledger_only_legitimacy_exhaustive():
    """thm:philosophy-empirical-stability-not-ledger-only-legitimacy; Lean: BEDC.GroundCompiler.NameCertGenerated.NameCertStabilitySoundnessEvent and BEDC.GroundCompiler.AnalysisPipeline.AnalysisEvidenceKind.nameCertFlow."""
    required = frozenset({SOURCE, CLASSIFIER, STABILITY, LEDGER})
    for empirical_stability, certificate, recorded_rows, open_rows in product(
        (False, True),
        (CERTIFIED, UNCERTIFIED),
        powerset(required),
        (frozenset(), frozenset({STABILITY})),
    ):
        candidate = profile(
            certificate=certificate,
            mode_rows=required,
            declared_mode_rows=required,
            open_mode_rows=open_rows,
            ledger_required_rows=required,
            ledger_recorded_rows=recorded_rows,
            empirical_stability=empirical_stability,
        )
        expected = (
            certificate.get("cert_status") == "certified"
            and open_rows == frozenset()
            and required.issubset(recorded_rows)
        )

        assert ledger_only_classifier(candidate) == expected

    stable_without_ledger = profile(empirical_stability=True, ledger_recorded_rows=frozenset({SOURCE}))
    legitimate_without_stability = profile(empirical_stability=False)
    assert stable_without_ledger.empirical_stability
    assert not ledger_only_classifier(stable_without_ledger)
    assert not legitimate_without_stability.empirical_stability
    assert ledger_only_classifier(legitimate_without_stability)


def test_not_every_hardenable_row_immediate_exhaustive():
    """thm:philosophy-not-every-hardenable-row-immediate; Lean: BEDC.GroundCompiler.MetricsFlow.MetricCertificateFlow and BEDC.GroundCompiler.AnalysisPipeline.StageLedgerAudit."""
    backend = HardeningBackend("lean", frozenset({SOURCE, CLASSIFIER, VERIFICATION}))
    gain_options = (-1.0, 0.0, 0.25)
    for row in UNIVERSE:
        for gain in gain_options:
            net_gain = {row: gain}
            expected = row in backend.hardenable_rows and gain > 0.0

            assert should_harden_immediately(backend, row, net_gain) == expected

    ledger_gap_profile = profile(
        ledger_required_rows=frozenset({SOURCE, CLASSIFIER}),
        ledger_recorded_rows=frozenset({SOURCE}),
        critical_rows=frozenset({SOURCE, CLASSIFIER}),
        hardened_rows=frozenset({SOURCE}),
    )
    assert backend_relative_hardenable(backend, CLASSIFIER)
    assert not should_harden_immediately(backend, CLASSIFIER, {CLASSIFIER: 0.0})
    assert hardening_frontier(
        profile(frontier_rows=frozenset({CLASSIFIER}), hardened_rows=frozenset({SOURCE})),
        backend,
    ) == frozenset({CLASSIFIER})
    assert not ledger_complete(ledger_gap_profile.ledger_required_rows, ledger_gap_profile.ledger_recorded_rows)
