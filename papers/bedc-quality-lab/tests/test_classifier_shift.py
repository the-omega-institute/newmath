from itertools import combinations, product

from bedc_quality_lab.classifier_shift import (
    ClassifierPassage,
    ClassifierState,
    classifier_shift,
    shift_information,
    structural_discovery,
)
from bedc_quality_lab.ledger import LedgerRowKey


SOURCE_IDS = frozenset({"a", "b", "c"})
SHIFT_ROW = LedgerRowKey("classifier", "a->b")
POLICY = frozenset({SHIFT_ROW})
CERTIFIED = {"cert_status": "certified"}
UNCERTIFIED = {"cert_status": "uncertified"}
BASE_RELATION = frozenset({
    ("a", "a", "same"),
    ("a", "b", "near"),
    ("b", "a", "near"),
    ("b", "b", "same"),
    ("c", "c", "same"),
})
SHIFTED_RELATION = frozenset({
    ("a", "a", "same"),
    ("a", "b", "far"),
    ("b", "a", "near"),
    ("b", "b", "same"),
    ("c", "c", "same"),
})


def powerset(rows):
    for size in range(len(rows) + 1):
        for members in combinations(rows, size):
            yield frozenset(members)


def state(
    *,
    relation=BASE_RELATION,
    certificate=CERTIFIED,
    ledger_policy=POLICY,
    surface_used=frozenset({("a", "b")}),
    verification_status="unchecked",
    record_count=1,
    feature_count=1,
    notation="plain",
):
    return ClassifierState(
        source_ids=SOURCE_IDS,
        pattern_id="finite-classifier",
        ledger_policy=ledger_policy,
        relation=relation,
        certificate=certificate,
        surface_used=surface_used,
        verification_status=verification_status,
        record_count=record_count,
        feature_count=feature_count,
        notation=notation,
    )


def passage(target, recorded_rows=POLICY):
    return ClassifierPassage(source=state(), target=target, recorded_rows=recorded_rows)


def test_discovery_requires_classifier_shift_exhaustive():
    """thm:philosophy-discovery-requires-classifier-shift; Lean: BEDC.GroundCompiler.NameCertGenerated.NameCertClassifierSoundnessEvent and BEDC.GroundCompiler.TheoremGenerated.CertificateSoundTheoremRecognition."""
    relations = (BASE_RELATION, SHIFTED_RELATION)
    surfaces = (frozenset(), frozenset({("a", "b")}))
    certificates = (CERTIFIED, UNCERTIFIED)
    policies = (frozenset(), POLICY)
    recorded_options = tuple(powerset((SHIFT_ROW,)))

    for relation, surface_used, certificate, ledger_policy, recorded_rows in product(
        relations,
        surfaces,
        certificates,
        policies,
        recorded_options,
    ):
        candidate = passage(
            state(
                relation=relation,
                surface_used=surface_used,
                certificate=certificate,
                ledger_policy=ledger_policy,
            ),
            recorded_rows=recorded_rows,
        )
        if structural_discovery(candidate):
            assert classifier_shift(candidate)

    no_shift = passage(state(relation=BASE_RELATION), recorded_rows=POLICY)
    assert not classifier_shift(no_shift)
    assert not structural_discovery(no_shift)


def test_discovery_requires_certificate_and_ledger_exhaustive():
    """thm:philosophy-discovery-requires-certificate-ledger; Lean: BEDC.GroundCompiler.NameCertGenerated.LedgerCompleteNameCertFlow and BEDC.GroundCompiler.TheoremGenerated.LedgerSoundTheoremRecognition."""
    for certificate, recorded_rows in product((CERTIFIED, UNCERTIFIED), powerset((SHIFT_ROW,))):
        candidate = passage(
            state(relation=SHIFTED_RELATION, certificate=certificate),
            recorded_rows=recorded_rows,
        )
        expected = certificate["cert_status"] == "certified" and SHIFT_ROW in recorded_rows
        assert structural_discovery(candidate) == expected

    uncertified = passage(state(relation=SHIFTED_RELATION, certificate=UNCERTIFIED))
    incomplete_ledger = passage(state(relation=SHIFTED_RELATION), recorded_rows=frozenset())
    assert not structural_discovery(uncertified)
    assert not structural_discovery(incomplete_ledger)


def test_formal_hardening_not_classifier_shift_exhaustive():
    """thm:philosophy-formal-hardening-not-classifier-shift; Lean: BEDC.GroundCompiler.AnalysisPipeline.CertificateObligationDischarge and BEDC.GroundCompiler.TheoremGenerated.StatusSoundTheoremRecognition."""
    for verification_status, record_count, feature_count, notation in product(
        ("unchecked", "kernel-checked"),
        (1, 2, 3),
        (1, 4),
        ("plain", "symbolic", "compressed"),
    ):
        candidate = passage(
            state(
                relation=BASE_RELATION,
                verification_status=verification_status,
                record_count=record_count,
                feature_count=feature_count,
                notation=notation,
            ),
            recorded_rows=POLICY,
        )
        assert not classifier_shift(candidate)
        assert not structural_discovery(candidate)
        assert shift_information(candidate) == 0


def test_classifier_shift_information_principle_exhaustive():
    """thm:philosophy-classifier-shift-information-principle; Lean: BEDC.GroundCompiler.NameCertGenerated.NameCertRecognitionRelation and BEDC.GroundCompiler.ChapterFlow.LedgerSound."""
    positive = passage(state(relation=SHIFTED_RELATION), recorded_rows=POLICY)
    assert shift_information(positive) == 1

    for certificate, recorded_rows, surface_used in product(
        (CERTIFIED, UNCERTIFIED),
        powerset((SHIFT_ROW,)),
        (frozenset(), frozenset({("a", "b")})),
    ):
        candidate = passage(
            state(
                relation=SHIFTED_RELATION,
                certificate=certificate,
                surface_used=surface_used,
            ),
            recorded_rows=recorded_rows,
        )
        expected = int(
            certificate["cert_status"] == "certified"
            and SHIFT_ROW in recorded_rows
            and ("a", "b") in surface_used
        )
        assert shift_information(candidate) == expected

    inert_changes = (
        state(record_count=9),
        state(feature_count=7),
        state(notation="renamed"),
        state(verification_status="kernel-checked"),
    )
    for target in inert_changes:
        assert shift_information(passage(target, recorded_rows=POLICY)) == 0
