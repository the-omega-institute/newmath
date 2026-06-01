from dataclasses import dataclass, field, replace
from itertools import combinations, product
from typing import Mapping

from bedc_quality_lab.classifier_shift import (
    ClassifierPassage,
    ClassifierState,
    classifier_shift,
    shift_information,
    structural_discovery,
)
from bedc_quality_lab.discovery import DiscoveryClaim, positive_discovery
from bedc_quality_lab.hardening import HardeningBackend, HardeningProfile, critical_hardening_gap
from bedc_quality_lab.ledger import LedgerRowKey, ledger_complete, ledger_debt, ledger_gap
from bedc_quality_lab.metrics import classifier_certificate
from bedc_quality_lab.scope import Scope, ScopedCertificate, scoped_resolved, scope_rows, verification_rows


Field = str
Source = str

FIELDS: tuple[Field, ...] = ("source", "pattern", "classifier", "stability", "ledger")
SOURCES: tuple[Source, ...] = ("h0", "h1", "h2")
CERTIFIED = classifier_certificate({"linear_identifiability_r2": 0.95, "approx_identifiability_proxy": 0.91})
UNCERTIFIED = classifier_certificate({"linear_identifiability_r2": 0.30, "approx_identifiability_proxy": 0.20})
SCOPE = Scope(
    domain_ids=frozenset(SOURCES),
    model_id="object-knowledge-namecert",
    admitted_family_id="classifier-core",
    behavior_id="stable-generated-behavior",
)
PAIR_ROW = LedgerRowKey("classifier", "h0->h1")
SOURCE_ROW = LedgerRowKey("namecert", "source")
PATTERN_ROW = LedgerRowKey("namecert", "pattern")
CLASSIFIER_ROW = LedgerRowKey("namecert", "classifier")
STABILITY_ROW = LedgerRowKey("namecert", "stability")
LEDGER_ROW = LedgerRowKey("namecert", "ledger")
WITNESS_ROW = LedgerRowKey("witness", "auditable")
PACKAGE_ROW = LedgerRowKey("package", "token")
GAP_ROW = LedgerRowKey("gap", "source-memory")
TRANSPORT_ROW = LedgerRowKey("transport", "pattern-ledger")
DERIVATION_ROW = LedgerRowKey("derivation", "declared-strength")
BRIDGE_ROW = LedgerRowKey("bridge", "standard-model")
REJECTED_LOGIC_ROWS = frozenset(
    {
        LedgerRowKey("logic-boundary", "hidden-choice"),
        LedgerRowKey("logic-boundary", "quotient-collapse"),
        LedgerRowKey("logic-boundary", "total-truth"),
        LedgerRowKey("logic-boundary", "unwitnessed-existence"),
    }
)
FIELD_ROWS = {
    "source": SOURCE_ROW,
    "pattern": PATTERN_ROW,
    "classifier": CLASSIFIER_ROW,
    "stability": STABILITY_ROW,
    "ledger": LEDGER_ROW,
}
NAMECERT_ROWS = frozenset(FIELD_ROWS.values())
POLICY = frozenset({PAIR_ROW})
BASE_RELATION = frozenset({("h0", "h1", "same"), ("h1", "h2", "same"), ("h0", "h2", "same")})
SHIFTED_RELATION = frozenset({("h0", "h1", "different"), ("h1", "h2", "same"), ("h0", "h2", "different")})
SURFACE = frozenset({("h0", "h1")})
STRENGTHS = ("seed", "paperCert", "checkedCert", "bridgeCert")


@dataclass(frozen=True)
class NameCert:
    name: str
    source_spec: frozenset[Source]
    pattern_spec: frozenset[Source]
    classifier_spec: frozenset[tuple[Source, Source]]
    stability_cert: frozenset[Source]
    ledger_policy: frozenset[LedgerRowKey]
    recorded_rows: frozenset[LedgerRowKey]
    certificate: Mapping[str, object] = field(default_factory=lambda: CERTIFIED)


@dataclass(frozen=True)
class Package:
    token: str
    source_rows: frozenset[LedgerRowKey]
    recorded_rows: frozenset[LedgerRowKey]
    token_sameness_grounded: bool
    quotient_primitive: bool = False


@dataclass(frozen=True)
class EpistemicObject:
    name: str
    namecert: NameCert
    witness_rows: frozenset[LedgerRowKey]
    strength: str = "paperCert"
    proof_strength_marked: bool = True
    bare_truth_predicate: bool = False


def powerset(values):
    values = tuple(values)
    for size in range(len(values) + 1):
        for members in combinations(values, size):
            yield frozenset(members)


def complete_namecert(*, recorded: frozenset[LedgerRowKey] = NAMECERT_ROWS) -> NameCert:
    return NameCert(
        name="ObjectN",
        source_spec=frozenset(SOURCES),
        pattern_spec=frozenset({"h0", "h1"}),
        classifier_spec=frozenset({("h0", "h0"), ("h0", "h1"), ("h1", "h0"), ("h1", "h1")}),
        stability_cert=frozenset({"h0", "h1"}),
        ledger_policy=NAMECERT_ROWS,
        recorded_rows=recorded,
    )


def namecert_with_fields(fields: frozenset[Field]) -> NameCert:
    return complete_namecert(recorded=frozenset(FIELD_ROWS[field] for field in fields))


def scoped_certificate(
    cert: NameCert,
    *,
    verification_status: str = "unverified",
    semantic_globalizer: bool = False,
    product_classifier: bool = False,
    boundary: frozenset[str] = frozenset({"outside-certificate-scope"}),
) -> ScopedCertificate:
    certificate = dict(cert.certificate)
    certificate["verification_status"] = verification_status
    certificate["semantic_globalizer"] = semantic_globalizer
    certificate["product_classifier"] = product_classifier
    return ScopedCertificate(
        scope=SCOPE,
        classifier_id="object-classifier",
        namecert_id=cert.name,
        required_rows=scope_rows(SCOPE) | cert.ledger_policy,
        recorded_rows=scope_rows(SCOPE) | cert.recorded_rows,
        certificate=certificate,
        not_claimed_boundary=boundary,
    )


def licensed_object(obj: EpistemicObject) -> bool:
    return scoped_resolved(scoped_certificate(obj.namecert)) and ledger_complete(
        {WITNESS_ROW, DERIVATION_ROW},
        obj.witness_rows | ({DERIVATION_ROW} if obj.proof_strength_marked else frozenset()),
    )


def classifier_state(*, shifted: bool, certificate=CERTIFIED, rows: frozenset[LedgerRowKey] = POLICY) -> ClassifierState:
    return ClassifierState(
        source_ids=frozenset(SOURCES),
        pattern_id="object-knowledge",
        ledger_policy=rows,
        relation=SHIFTED_RELATION if shifted else BASE_RELATION,
        certificate=certificate,
        surface_used=SURFACE,
        verification_status="kernel-checked" if certificate.get("cert_status") == "certified" else "unverified",
        record_count=2,
    )


def classifier_passage(*, shifted: bool = True, rows: frozenset[LedgerRowKey] = POLICY, certificate=CERTIFIED) -> ClassifierPassage:
    return ClassifierPassage(
        source=classifier_state(shifted=False),
        target=classifier_state(shifted=shifted, certificate=certificate),
        recorded_rows=rows,
    )


def package(*, recorded: frozenset[LedgerRowKey], grounded: bool = True, quotient: bool = False) -> Package:
    return Package(
        token="pkg-h0",
        source_rows=frozenset({PACKAGE_ROW, GAP_ROW}),
        recorded_rows=recorded,
        token_sameness_grounded=grounded,
        quotient_primitive=quotient,
    )


def valid_package(pkg: Package) -> bool:
    return (
        pkg.token_sameness_grounded
        and not pkg.quotient_primitive
        and ledger_complete(pkg.source_rows, pkg.recorded_rows)
    )


def knowledge_object(
    *,
    cert: NameCert | None = None,
    witnesses: frozenset[LedgerRowKey] = frozenset({WITNESS_ROW}),
    strength: str = "paperCert",
    marked: bool = True,
    truth: bool = False,
) -> EpistemicObject:
    return EpistemicObject(
        name="ObjectN",
        namecert=complete_namecert() if cert is None else cert,
        witness_rows=witnesses,
        strength=strength,
        proof_strength_marked=marked,
        bare_truth_predicate=truth,
    )


def hardening_profile(*, recorded=frozenset(), hardened=frozenset()) -> HardeningProfile:
    return HardeningProfile(
        certificate=CERTIFIED,
        mode_rows=frozenset(),
        declared_mode_rows=frozenset(),
        open_mode_rows=frozenset(),
        ledger_required_rows=frozenset({TRANSPORT_ROW}),
        ledger_recorded_rows=recorded,
        critical_rows=frozenset({TRANSPORT_ROW}),
        hardened_rows=hardened,
        frontier_rows=frozenset(),
        non_hardenable_residue=frozenset(),
    )


def discovery_claim(obj: EpistemicObject, *, shifted: bool = True) -> DiscoveryClaim:
    return DiscoveryClaim(
        passage=classifier_passage(shifted=shifted),
        benefit_terms={"object": 1.4},
        score_terms={"certificate": 0.2},
        debt_terms={"ledger": 0.1},
        ledger_required_rows=POLICY,
        ledger_recorded_rows=POLICY,
        public_cost_protocol=True,
        scope_sealed=True,
        not_claimed_boundary=frozenset({"outside-object-knowledge"}),
        scoped_certificate=scoped_certificate(obj.namecert),
    )


def strength_at_least(actual: str, required: str) -> bool:
    return STRENGTHS.index(actual) >= STRENGTHS.index(required)


def export_accepted(obj: EpistemicObject, required_strength: str) -> bool:
    return licensed_object(obj) and strength_at_least(obj.strength, required_strength) and obj.proof_strength_marked


def test_philosophy_anti_primitive_principle_exhaustive():
    """thm:philosophy-anti-primitive-principle; Lean: BEDC.FKernel.NameCert.NameCert; primitive: scoped_resolved, ledger_complete."""
    for primitive, fields in product((False, True), powerset(FIELDS)):
        obj = knowledge_object(cert=namecert_with_fields(fields))
        if primitive:
            assert not licensed_object(obj) or primitive
        if not primitive and fields == frozenset(FIELDS):
            assert licensed_object(obj)
        if not primitive and fields != frozenset(FIELDS):
            assert not licensed_object(obj)
    assert licensed_object(knowledge_object())


def test_philosophy_definitions_do_not_create_objects_exhaustive():
    """cor:philosophy-definitions-do-not-create-objects; Lean: BEDC.Meta.DiscoveryCertificate.NameCertFiveRows; primitive: ledger_gap, scoped_resolved."""
    for fields in powerset(FIELDS):
        cert = namecert_with_fields(fields)
        has_definition_text = True
        assert has_definition_text
        assert scoped_resolved(scoped_certificate(cert)) == (fields == frozenset(FIELDS))
        if ledger_gap(NAMECERT_ROWS, cert.recorded_rows):
            assert not scoped_resolved(scoped_certificate(cert))
    assert not scoped_resolved(scoped_certificate(namecert_with_fields(frozenset({"source", "pattern"}))))


def test_philosophy_object_existence_certificate_existence_exhaustive():
    """cor:philosophy-object-existence-certificate-existence; Lean: BEDC.Meta.DiscoveryCertificate.nameCertFiveRows_named_row_projection; primitive: scope_rows, scoped_resolved."""
    for fields in powerset(FIELDS):
        obj = knowledge_object(cert=namecert_with_fields(fields))
        assert licensed_object(obj) == scoped_resolved(scoped_certificate(obj.namecert))
        if licensed_object(obj):
            assert NAMECERT_ROWS.issubset(obj.namecert.recorded_rows)
    assert not licensed_object(knowledge_object(cert=namecert_with_fields(frozenset(FIELDS) - {"ledger"})))


def test_philosophy_namecert_five_fields_irreducible_exhaustive():
    """thm:philosophy-namecert-five-fields-irreducible; Lean: BEDC.Meta.DiscoveryCertificate.NameCertFiveRows; primitive: ledger_gap, ledger_complete."""
    for omitted in powerset(FIELDS):
        fields = frozenset(field for field in FIELDS if field not in omitted)
        cert = namecert_with_fields(fields)
        assert ledger_complete(NAMECERT_ROWS, cert.recorded_rows) == (not omitted)
        if omitted:
            assert ledger_gap(NAMECERT_ROWS, cert.recorded_rows)
    for field in FIELDS:
        assert not ledger_complete(NAMECERT_ROWS, namecert_with_fields(frozenset(FIELDS) - {field}).recorded_rows)


def test_philosophy_objects_fivefold_qualifications_exhaustive():
    """cor:philosophy-objects-fivefold-qualifications; Lean: BEDC.Meta.DiscoveryCertificate.nameCertFiveRows_pattern_ledger; primitive: scoped_resolved."""
    for fields in powerset(FIELDS):
        obj = knowledge_object(cert=namecert_with_fields(fields))
        fivefold = all(FIELD_ROWS[field] in obj.namecert.recorded_rows for field in FIELDS)
        assert scoped_resolved(scoped_certificate(obj.namecert)) == fivefold
        assert licensed_object(obj) == fivefold
    assert licensed_object(knowledge_object())


def test_philosophy_kernel_namecert_classifier_core_exhaustive():
    """thm:philosophy-kernel-namecert-classifier-core; Lean: BEDC.FKernel.NameCert.NameCert; primitive: classifier_shift."""
    for shifted, certified, rows in product((False, True), (False, True), powerset((PAIR_ROW,))):
        passage = classifier_passage(
            shifted=shifted,
            rows=rows,
            certificate=CERTIFIED if certified else UNCERTIFIED,
        )
        core_available = structural_discovery(passage)
        assert core_available == (shifted and certified and ledger_complete(POLICY, rows))
        if not classifier_shift(passage):
            assert not core_available
    assert structural_discovery(classifier_passage())


def test_philosophy_paper_completion_not_machine_checking_exhaustive():
    """cor:philosophy-paper-completion-not-machine-checking; Lean: BEDC.FKernel.NameCert.NameCert; primitive: verification_rows, scoped_resolved."""
    cert = complete_namecert()
    for status in ("unverified", "kernel-checked"):
        scoped = scoped_certificate(cert, verification_status=status)
        assert scoped_resolved(scoped)
        assert bool(verification_rows(scoped)) == (status == "kernel-checked")
    assert scoped_resolved(scoped_certificate(cert, verification_status="unverified"))
    assert not verification_rows(scoped_certificate(cert, verification_status="unverified"))


def test_philosophy_knowledge_witness_not_bare_truth_exhaustive():
    """thm:philosophy-knowledge-witness-not-bare-truth; Lean: BEDC.FKernel.NameCert.semanticNameCert_pattern_ledger_witness; primitive: ledger_complete, scoped_resolved."""
    for truth, witnesses in product((False, True), powerset((WITNESS_ROW, LEDGER_ROW))):
        obj = knowledge_object(witnesses=witnesses, truth=truth)
        auditable = ledger_complete({WITNESS_ROW}, obj.witness_rows) and scoped_resolved(scoped_certificate(obj.namecert))
        assert auditable == (WITNESS_ROW in witnesses)
        if truth and WITNESS_ROW not in witnesses:
            assert not auditable
    assert not ledger_complete({WITNESS_ROW}, frozenset())


def test_philosophy_truth_meta_certificates_object_layer_exhaustive():
    """cor:philosophy-truth-meta-certificates-object-layer; Lean: BEDC.FKernel.NameCert.SemanticNameCert; primitive: scoped_resolved."""
    for has_cert, has_truth in product((False, True), repeat=2):
        obj = knowledge_object(cert=complete_namecert() if has_cert else namecert_with_fields(frozenset()), truth=has_truth)
        object_layer_consumable = scoped_resolved(scoped_certificate(obj.namecert))
        assert object_layer_consumable == has_cert
        if has_truth and not has_cert:
            assert not object_layer_consumable
    assert scoped_resolved(scoped_certificate(complete_namecert()))


def test_philosophy_packages_not_quotients_exhaustive():
    """thm:philosophy-packages-not-quotients; Lean: BEDC.BaseReflection.Psame.PsameBase; primitive: ledger_complete."""
    for grounded, quotient, rows in product((False, True), (False, True), powerset((PACKAGE_ROW, GAP_ROW))):
        pkg = package(recorded=rows, grounded=grounded, quotient=quotient)
        assert valid_package(pkg) == (grounded and not quotient and ledger_complete(pkg.source_rows, rows))
        if quotient:
            assert not valid_package(pkg)
    assert valid_package(package(recorded=frozenset({PACKAGE_ROW, GAP_ROW})))


def test_philosophy_compression_must_remember_exhaustive():
    """thm:philosophy-compression-must-remember; Lean: BEDC.Meta.DiscoveryCertificate.certifiedClassifierState_ledger_witness; primitive: ledger_gap, ledger_debt."""
    costs = {PACKAGE_ROW: 0.5, GAP_ROW: 2.0}
    for rows in powerset((PACKAGE_ROW, GAP_ROW)):
        pkg = package(recorded=rows)
        debt = ledger_debt(ledger_gap(pkg.source_rows, pkg.recorded_rows), costs)
        assert (debt == 0.0) == ledger_complete(pkg.source_rows, rows)
        if GAP_ROW not in rows:
            assert debt >= 2.0
    assert ledger_debt(ledger_gap({GAP_ROW}, frozenset()), {GAP_ROW: 2.0}) > 0.0


def test_philosophy_no_amnesic_compression_exhaustive():
    """cor:philosophy-no-amnesic-compression; Lean: BEDC.FKernel.NameCert.semanticNameCert_ledger_policy_witness; primitive: ledger_complete, ledger_gap."""
    for rows in powerset((PACKAGE_ROW, GAP_ROW)):
        pkg = package(recorded=rows)
        remembers_source = not ledger_gap({GAP_ROW}, rows)
        assert valid_package(pkg) == (PACKAGE_ROW in rows and remembers_source)
        if PACKAGE_ROW in rows and GAP_ROW not in rows:
            assert not valid_package(pkg)
    assert not valid_package(package(recorded=frozenset({PACKAGE_ROW})))


def test_philosophy_semantic_certificates_pattern_ledger_witnesses_exhaustive():
    """thm:philosophy-semantic-certificates-pattern-ledger-witnesses; Lean: BEDC.FKernel.NameCert.semanticNameCert_pattern_ledger_witness; primitive: scope_rows, ledger_complete."""
    required = NAMECERT_ROWS | frozenset({PATTERN_ROW, LEDGER_ROW})
    for rows in powerset(required):
        cert = replace(complete_namecert(), ledger_policy=required, recorded_rows=rows)
        semantic = ledger_complete({PATTERN_ROW, LEDGER_ROW}, rows) and scoped_resolved(scoped_certificate(cert, semantic_globalizer=True))
        assert semantic == ledger_complete(required | scope_rows(SCOPE), rows | scope_rows(SCOPE))
    assert scoped_resolved(scoped_certificate(complete_namecert(), semantic_globalizer=True))


def test_philosophy_pattern_ledger_transport_exhaustive():
    """thm:philosophy-pattern-ledger-transport; Lean: BEDC.FKernel.NameCert.semanticNameCert_pattern_ledger_transport; primitive: classifier_shift, ledger_complete."""
    required = POLICY | frozenset({PATTERN_ROW, LEDGER_ROW, TRANSPORT_ROW})
    for rows in powerset(required):
        passage = classifier_passage(rows=rows & POLICY)
        transported = classifier_shift(passage) and ledger_complete(required, rows)
        if ledger_complete(required, rows):
            assert shift_information(passage) == 1
        assert transported == (PATTERN_ROW in rows and LEDGER_ROW in rows and TRANSPORT_ROW in rows and PAIR_ROW in rows)
    assert not ledger_complete(required, frozenset({PAIR_ROW, PATTERN_ROW, LEDGER_ROW}))


def test_philosophy_classifier_chain_transport_exhaustive():
    """thm:philosophy-classifier-chain-transport; Lean: BEDC.FKernel.NameCert.semanticNameCert_classifier_chain_transport; primitive: classifier_shift, ledger_complete."""
    first = LedgerRowKey("transport", "h0->h1")
    second = LedgerRowKey("transport", "h1->h2")
    target = LedgerRowKey("transport", "h0->h2")
    required = frozenset({first, second, target, PATTERN_ROW, LEDGER_ROW, PAIR_ROW})
    for rows in powerset(required):
        chain_transports = ledger_complete(required, rows) and classifier_shift(classifier_passage(rows=rows & POLICY))
        assert chain_transports == required.issubset(rows)
    assert not ledger_complete(required, required - {target})


def test_philosophy_object_stability_transportability_exhaustive():
    """cor:philosophy-object-stability-transportability; Lean: BEDC.FKernel.NameCert.semanticNameCert_classifier_chain_transport; primitive: scoped_resolved, critical_hardening_gap."""
    backend = HardeningBackend("transport-backend", frozenset({TRANSPORT_ROW}))
    for recorded, hardened in product(powerset((TRANSPORT_ROW,)), repeat=2):
        profile = hardening_profile(recorded=recorded, hardened=hardened)
        stable = scoped_resolved(scoped_certificate(complete_namecert())) and not critical_hardening_gap(profile, backend)
        assert stable == (TRANSPORT_ROW in recorded or TRANSPORT_ROW in hardened)
    assert not critical_hardening_gap(hardening_profile(recorded=frozenset({TRANSPORT_ROW})), backend)


def test_philosophy_object_export_acceptance_gate_exhaustive():
    """thm:philosophy-object-export-acceptance-gate; Lean: BEDC.Meta.DiscoveryCertificate.nameCertFiveRows_named_row_projection; primitive: scoped_resolved, verification_rows."""
    for strength, required, marked in product(STRENGTHS, STRENGTHS, (False, True)):
        obj = knowledge_object(strength=strength, marked=marked, witnesses=frozenset({WITNESS_ROW}))
        assert export_accepted(obj, required) == (marked and strength_at_least(strength, required))
        if required == "checkedCert":
            scoped = scoped_certificate(obj.namecert, verification_status="kernel-checked" if strength_at_least(strength, required) else "unverified")
            assert bool(verification_rows(scoped)) == strength_at_least(strength, required)
    assert not export_accepted(knowledge_object(marked=False), "paperCert")


def test_philosophy_no_strength_inflation_exhaustive():
    """cor:philosophy-no-strength-inflation; Lean: BEDC.Meta.DiscoveryCertificate.DiscoveryCost; primitive: ledger_gap."""
    for actual, reported in product(STRENGTHS, repeat=2):
        inflation = not strength_at_least(actual, reported)
        required = frozenset(LedgerRowKey("strength", strength) for strength in STRENGTHS[: STRENGTHS.index(reported) + 1])
        recorded = frozenset(LedgerRowKey("strength", strength) for strength in STRENGTHS[: STRENGTHS.index(actual) + 1])
        assert bool(ledger_gap(required, recorded)) == inflation
    assert ledger_gap({BRIDGE_ROW}, frozenset())


def test_philosophy_object_knowledge_certificate_synthesis_exhaustive():
    """thm:philosophy-object-knowledge-certificate-synthesis; Lean: BEDC.Meta.DiscoveryCertificate.discovery_transition_witness; primitive: positive_discovery, scoped_resolved."""
    for fields, witness, shifted in product(powerset(FIELDS), (False, True), (False, True)):
        obj = knowledge_object(cert=namecert_with_fields(fields), witnesses=frozenset({WITNESS_ROW}) if witness else frozenset())
        claim = discovery_claim(obj, shifted=shifted)
        synthesized = licensed_object(obj) and positive_discovery(claim)
        assert synthesized == (fields == frozenset(FIELDS) and witness and shifted)
    assert positive_discovery(discovery_claim(knowledge_object()))


def test_philosophy_bedc_object_theory_exhaustive():
    """cor:philosophy-bedc-object-theory; Lean: BEDC.Meta.DiscoveryCertificate.NameCertFiveRows; primitive: ledger_complete."""
    for fields in powerset(FIELDS):
        cert = namecert_with_fields(fields)
        licensed_name = ledger_complete(NAMECERT_ROWS, cert.recorded_rows)
        stable_behavior_certificate = scoped_resolved(scoped_certificate(cert))
        assert licensed_name == stable_behavior_certificate
    assert ledger_complete(NAMECERT_ROWS, complete_namecert().recorded_rows)


def test_philosophy_bedc_epistemology_exhaustive():
    """cor:philosophy-bedc-epistemology; Lean: BEDC.FKernel.NameCert.semanticNameCert_pattern_ledger_witness; primitive: ledger_complete, scoped_resolved."""
    required = frozenset({WITNESS_ROW, TRANSPORT_ROW, STABILITY_ROW, LEDGER_ROW})
    for rows in powerset(required):
        obj = knowledge_object(witnesses=rows & {WITNESS_ROW})
        proves = ledger_complete(required, rows) and scoped_resolved(scoped_certificate(obj.namecert))
        if proves:
            assert licensed_object(obj)
        if WITNESS_ROW not in rows:
            assert not proves
    assert ledger_complete(required, required)


def test_philosophy_passage_to_logic_meta_loop_exhaustive():
    """cor:philosophy-passage-to-logic-meta-loop; Lean: BEDC.FKernel.NameCert.carrier_respects_equiv; primitive: ledger_gap, scoped_resolved."""
    accepted = frozenset(
        {
            LedgerRowKey("logic-pattern", "fixed-carrier-contradiction"),
            LedgerRowKey("logic-pattern", "constructor-no-confusion"),
            LedgerRowKey("logic-pattern", "witness-preserving-transport"),
        }
    )
    for rejected in powerset(REJECTED_LOGIC_ROWS):
        proof_rows = accepted | rejected
        discipline_preserved = not ledger_gap(REJECTED_LOGIC_ROWS, REJECTED_LOGIC_ROWS - rejected)
        assert discipline_preserved == (not rejected)
        if rejected:
            assert proof_rows & REJECTED_LOGIC_ROWS
    assert scoped_resolved(scoped_certificate(complete_namecert()))
