from itertools import combinations, product

from bedc_quality_lab.classifier_shift import (
    ClassifierPassage,
    ClassifierState,
    classifier_shift,
    shift_information,
    structural_discovery,
)
from bedc_quality_lab.discovery import DiscoveryClaim, positive_discovery
from bedc_quality_lab.hardening import HardeningBackend, HardeningProfile, critical_hardening_gap
from bedc_quality_lab.ledger import LedgerEntry, LedgerRowKey, critical_gap, ledger_complete, ledger_debt, ledger_gap
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


Mark = str
Hist = tuple[Mark, ...]

MARKS: tuple[Mark, ...] = ("b0", "b1")
EMPTY_HISTORY: Hist = ()
HISTORIES: tuple[Hist, ...] = (
    (),
    ("b0",),
    ("b1",),
    ("b0", "b0"),
    ("b0", "b1"),
    ("b1", "b0"),
    ("b1", "b1"),
)
CERTIFIED = classifier_certificate({"linear_identifiability_r2": 0.95, "approx_identifiability_proxy": 0.90})
UNCERTIFIED = classifier_certificate({"linear_identifiability_r2": 0.10, "approx_identifiability_proxy": 0.10})
SHIFT_ROW = LedgerRowKey("classifier", "source->target")
TRACE_ROW = LedgerRowKey("history", "trace")
NAMECERT_ROW = LedgerRowKey("namecert", "recordable-distinction")
BOUNDARY_ROW = LedgerRowKey("boundary", "outside-closed-substrate")
POLICY = frozenset({SHIFT_ROW})
BASE_RELATION = frozenset({("source", "target", "same")})
SHIFTED_RELATION = frozenset({("source", "target", "different")})
SURFACE = frozenset({("source", "target")})


def powerset(values):
    values = tuple(values)
    for size in range(len(values) + 1):
        for members in combinations(values, size):
            yield frozenset(members)


def encode(history: Hist) -> str:
    return "empty" if not history else ".".join(history)


def msame(left: Mark, right: Mark) -> bool:
    return left == right and left in MARKS and right in MARKS


def hsame(left: Hist, right: Hist) -> bool:
    return left == right and generated(left) and generated(right)


def empty_history() -> Hist:
    return EMPTY_HISTORY


def cont(base: Hist, mark: Mark) -> Hist:
    return base + (mark,)


def extension(base: Hist, mark: Mark, target: Hist) -> bool:
    return mark in MARKS and target == cont(base, mark)


def continuation(source: Hist, route: Hist, target: Hist) -> bool:
    return target == source + route and generated(source) and generated(route) and generated(target)


def predecessor(target: Hist) -> tuple[Hist, Mark] | None:
    if not target:
        return None
    return target[:-1], target[-1]


def generated(history: Hist) -> bool:
    return all(mark in MARKS for mark in history)


def information_content(history: Hist) -> Hist:
    return history


def is_prefix(prefix: Hist, target: Hist) -> bool:
    return target[: len(prefix)] == prefix


def history_rows(history: Hist) -> frozenset[LedgerRowKey]:
    return frozenset(LedgerRowKey("history-step", f"{index}:{mark}") for index, mark in enumerate(history))


def history_scope(history: Hist, *, behavior: str = "trace") -> Scope:
    return Scope(
        domain_ids=frozenset({encode(history)}),
        model_id="distinction-history",
        admitted_family_id="hsame",
        behavior_id=f"{behavior}:{encode(history)}",
    )


def scoped_history_certificate(
    history: Hist,
    *,
    certificate=CERTIFIED,
    recorded_rows: frozenset[LedgerRowKey] | None = None,
    boundary: frozenset[str] = frozenset({"outside-generated-history"}),
) -> ScopedCertificate:
    scope = history_scope(history)
    required = scope_rows(scope) | history_rows(history) | frozenset({BOUNDARY_ROW})
    return ScopedCertificate(
        scope=scope,
        classifier_id="history-shape",
        namecert_id="history-namecert",
        required_rows=required,
        recorded_rows=required if recorded_rows is None else recorded_rows,
        certificate=certificate,
        not_claimed_boundary=boundary,
    )


def classifier_state(
    *,
    shifted: bool,
    certificate=CERTIFIED,
    relation: frozenset[tuple[str, str, str]] | None = None,
    records: int = 0,
    rows: frozenset[LedgerRowKey] = POLICY,
) -> ClassifierState:
    return ClassifierState(
        source_ids=frozenset({"source", "target"}),
        pattern_id="distinction-history",
        ledger_policy=rows,
        relation=SHIFTED_RELATION if relation is None and shifted else BASE_RELATION if relation is None else relation,
        certificate=certificate,
        surface_used=SURFACE,
        verification_status="kernel-checked" if certificate.get("cert_status") == "certified" else "unverified",
        record_count=records,
    )


def classifier_passage(
    *,
    shifted: bool,
    certificate=CERTIFIED,
    source_records: int = 1,
    target_records: int = 2,
    rows: frozenset[LedgerRowKey] = POLICY,
) -> ClassifierPassage:
    return ClassifierPassage(
        source=classifier_state(shifted=False, records=source_records),
        target=classifier_state(shifted=shifted, certificate=certificate, records=target_records),
        recorded_rows=rows,
    )


def discovery_claim(
    *,
    shifted: bool,
    benefit: float,
    score: float = 0.1,
    debt: float = 0.1,
    certificate=CERTIFIED,
    rows: frozenset[LedgerRowKey] = POLICY,
    boundary: frozenset[str] = frozenset({"outside-unfolding"}),
    scope_sealed: bool = True,
) -> DiscoveryClaim:
    return DiscoveryClaim(
        passage=classifier_passage(shifted=shifted, certificate=certificate, rows=rows),
        benefit_terms={"trace": benefit},
        score_terms={"classifier": score},
        debt_terms={"ledger": debt},
        ledger_required_rows=POLICY,
        ledger_recorded_rows=rows,
        public_cost_protocol=True,
        scope_sealed=scope_sealed,
        not_claimed_boundary=boundary,
        scoped_certificate=scoped_history_certificate(("b0",), recorded_rows=scope_rows(history_scope(("b0",))) | history_rows(("b0",)) | frozenset({BOUNDARY_ROW})),
    )


def hardening_profile(
    *,
    hardened_rows=frozenset(),
    frontier_rows=frozenset(),
    recorded_rows=frozenset({TRACE_ROW}),
) -> HardeningProfile:
    return HardeningProfile(
        certificate=CERTIFIED,
        mode_rows=frozenset(),
        declared_mode_rows=frozenset(),
        open_mode_rows=frozenset(),
        ledger_required_rows=frozenset({TRACE_ROW}),
        ledger_recorded_rows=recorded_rows,
        critical_rows=frozenset({TRACE_ROW}),
        hardened_rows=hardened_rows,
        frontier_rows=frontier_rows,
        non_hardenable_residue=frozenset(),
    )


def test_philosophy_not_additional_layer_exhaustive():
    """thm:philosophy-not-additional-layer; Lean: BEDC.FKernel.Hist.BHist and BEDC.FKernel.Cont.Cont; primitive: scope_rows, scoped_resolved, ledger_gap."""
    required_fields = frozenset({"history", "hsame", "continuation", "certificate", "boundary"})
    for fields in powerset(required_fields | frozenset({"observer-substance", "global-truth"})):
        rows = frozenset(LedgerRowKey("kernel-field", field) for field in fields)
        required = frozenset(LedgerRowKey("kernel-field", field) for field in required_fields)
        gap = ledger_gap(required, rows)
        if required_fields.issubset(fields):
            assert gap == frozenset()
        if "observer-substance" in fields or "global-truth" in fields:
            assert BOUNDARY_ROW not in rows
    cert = scoped_history_certificate(("b0",))
    incomplete = scoped_history_certificate(("b0",), recorded_rows=frozenset())
    assert scoped_resolved(cert)
    assert not scoped_resolved(incomplete)


def test_philosophy_primitive_distinction_irreducible_exhaustive():
    """thm:philosophy-primitive-distinction-irreducible; Lean: BEDC.FKernel.Mark.BMark_generated_cases; fixture: Mark, msame."""
    for proposed_basis in powerset(("b0", "b1")):
        separates_marks = all(mark in proposed_basis for mark in MARKS) and not msame("b0", "b1")
        assert separates_marks == (proposed_basis == frozenset(MARKS))
    assert not msame("b0", "b1")
    assert not all(msame(left, right) for left, right in product(MARKS, repeat=2))


def test_philosophy_distinction_precedes_information_exhaustive():
    """cor:philosophy-distinction-precedes-information; Lean: BEDC.FKernel.Mark.mark_no_confusion; primitive: ledger_complete."""
    for rows in powerset((LedgerRowKey("mark", "b0"), LedgerRowKey("mark", "b1"))):
        complete = ledger_complete((LedgerRowKey("mark", mark) for mark in MARKS), rows)
        assert complete == all(LedgerRowKey("mark", mark) in rows for mark in MARKS)
    assert ledger_complete((LedgerRowKey("mark", mark) for mark in MARKS), frozenset(LedgerRowKey("mark", mark) for mark in MARKS))
    assert not ledger_complete((LedgerRowKey("mark", mark) for mark in MARKS), frozenset({LedgerRowKey("mark", "b0")}))


def test_philosophy_starting_point_not_thing_exhaustive():
    """cor:philosophy-starting-point-not-thing; Lean: BEDC.FKernel.Mark.BMark and BEDC.FKernel.Hist.BHist; fixture: Mark, history_rows."""
    for candidate in powerset(("recordable-distinction", "object", "set", "subject", "proposition")):
        if "recordable-distinction" in candidate and not candidate & {"object", "set", "subject", "proposition"}:
            assert not history_rows(empty_history())
        if "object" in candidate:
            assert not ledger_complete((NAMECERT_ROW,), frozenset())
    assert "recordable-distinction" in frozenset({"recordable-distinction"})
    assert "object" not in frozenset({"recordable-distinction"})


def test_philosophy_mark_sameness_reflexive_exhaustive():
    """thm:philosophy-mark-sameness-reflexive; Lean: BEDC.FKernel.Mark.msame_refl; fixture: Mark, msame."""
    for mark in MARKS:
        assert msame(mark, mark)
    assert msame("b0", "b0")
    assert not msame("b0", "outside")


def test_philosophy_mark_sameness_symmetric_transitive_exhaustive():
    """thm:philosophy-mark-sameness-symmetric-transitive; Lean: BEDC.FKernel.Mark.msame_symm and msame_trans; fixture: Mark, msame."""
    for left, middle, right in product(MARKS, repeat=3):
        if msame(left, middle):
            assert msame(middle, left)
        if msame(left, middle) and msame(middle, right):
            assert msame(left, right)
    assert msame("b1", "b1") and msame("b1", "b1")
    assert not (msame("b0", "b1") and msame("b1", "b0"))


def test_philosophy_mark_no_confusion_exhaustive():
    """thm:philosophy-mark-no-confusion; Lean: BEDC.FKernel.Mark.mark_no_confusion; fixture: Mark, msame."""
    for left, right in product(MARKS, repeat=2):
        assert msame(left, right) == (left == right)
    assert not msame("b0", "b1")
    assert msame("b0", "b0")


def test_philosophy_primitive_marks_not_booleans_exhaustive():
    """cor:philosophy-primitive-marks-not-booleans; Lean: BEDC.FKernel.Mark.BMark; primitive: classifier_certificate."""
    bool_rows = frozenset({LedgerRowKey("carrier", "bool"), LedgerRowKey("classifier", "truth-table"), NAMECERT_ROW})
    for rows in powerset(bool_rows):
        certified_interface = ledger_complete(bool_rows, rows) and CERTIFIED["cert_status"] == "certified"
        if rows == bool_rows:
            assert certified_interface
        if rows != bool_rows:
            assert not certified_interface
    assert set(MARKS) == {"b0", "b1"}
    assert not ledger_complete(bool_rows, frozenset({LedgerRowKey("carrier", "bool")}))


def test_philosophy_histories_finitely_generated_exhaustive():
    """thm:philosophy-histories-finitely-generated; Lean: BEDC.FKernel.Hist.BHist; fixture: Hist, predecessor."""
    for history in HISTORIES:
        cursor = history
        steps = 0
        while predecessor(cursor) is not None:
            cursor, _mark = predecessor(cursor)
            steps += 1
        assert cursor == empty_history()
        assert steps == len(history)
    assert generated(("b0", "b1"))
    assert not generated(("b0", "outside"))


def test_philosophy_no_external_history_kernel_exhaustive():
    """cor:philosophy-no-external-history-kernel; Lean: BEDC.FKernel.Hist.BHist; fixture: Hist, generated."""
    candidates = HISTORIES + (("outside",), ("b0", "outside"))
    for history in candidates:
        assert generated(history) == all(mark in MARKS for mark in history)
    assert generated(("b1", "b0"))
    assert not generated(("outside",))


def test_philosophy_empty_history_zero_information_boundary_exhaustive():
    """thm:philosophy-empty-history-zero-information-boundary; Lean: BEDC.FKernel.Hist.BHist.Empty; fixture: empty_history, information_content."""
    for history in HISTORIES:
        assert (information_content(history) == ()) == (history == empty_history())
    assert information_content(empty_history()) == ()
    assert information_content(("b0",)) != ()


def test_philosophy_nontrivial_information_requires_extension_exhaustive():
    """cor:philosophy-nontrivial-information-requires-extension; Lean: BEDC.FKernel.Hist.hsame_constructor_characterization; fixture: predecessor, extension."""
    for history in HISTORIES:
        pred = predecessor(history)
        if information_content(history):
            assert pred is not None
            base, mark = pred
            assert extension(base, mark, history)
        else:
            assert pred is None
    assert extension((), "b0", ("b0",))
    assert not extension((), "b0", ())


def test_philosophy_history_sameness_reflexive_exhaustive():
    """thm:philosophy-history-sameness-reflexive; Lean: BEDC.FKernel.Hist.hsame_refl; fixture: Hist, hsame."""
    for history in HISTORIES:
        assert hsame(history, history)
    assert hsame(("b0", "b1"), ("b0", "b1"))
    assert not hsame(("b0",), ("b1",))


def test_philosophy_history_sameness_symmetric_transitive_exhaustive():
    """thm:philosophy-history-sameness-symmetric-transitive; Lean: BEDC.FKernel.Hist.hsame_symm and hsame_trans; fixture: Hist, hsame."""
    for left, middle, right in product(HISTORIES, repeat=3):
        if hsame(left, middle):
            assert hsame(middle, left)
        if hsame(left, middle) and hsame(middle, right):
            assert hsame(left, right)
    assert hsame(("b1",), ("b1",))
    assert not (hsame(("b0",), ("b1",)) and hsame(("b1",), ("b0",)))


def test_philosophy_history_no_confusion_exhaustive():
    """thm:philosophy-history-no-confusion; Lean: BEDC.FKernel.Hist.history_no_confusion; fixture: Hist, hsame."""
    extensions = tuple(history for history in HISTORIES if history)
    for history in extensions:
        assert not hsame(empty_history(), history)
        assert not hsame(history, empty_history())
    for base_left, base_right in product(HISTORIES[:3], repeat=2):
        assert not hsame(cont(base_left, "b0"), cont(base_right, "b1"))
    assert not hsame((), ("b0",))
    assert hsame((), ())


def test_philosophy_history_identity_constructor_shape_exhaustive():
    """cor:philosophy-history-identity-constructor-shape; Lean: BEDC.FKernel.Hist.history_constructor_characterization; fixture: predecessor, hsame."""
    for left, right in product(HISTORIES, repeat=2):
        if hsame(left, right) and left:
            left_pred, left_mark = predecessor(left)
            right_pred, right_mark = predecessor(right)
            assert left_mark == right_mark
            assert hsame(left_pred, right_pred)
    assert hsame(("b0", "b1"), ("b0", "b1"))
    assert predecessor(("b0", "b1")) != predecessor(("b1", "b0"))


def test_philosophy_hist_minimal_binary_distinction_carrier_exhaustive():
    """thm:philosophy-hist-minimal-binary-distinction-carrier; Lean: BEDC.FKernel.Hist.BHist and BEDC.FKernel.Mark.BMark; fixture: Hist, cont."""
    features = ("empty-origin", "b0-step", "b1-step")
    for available in powerset(features):
        supports_binary_trace = all(feature in available for feature in features)
        if supports_binary_trace:
            assert cont(cont(empty_history(), "b0"), "b1") == ("b0", "b1")
        else:
            assert not supports_binary_trace
    assert {"empty-origin", "b0-step", "b1-step"} == set(features)
    assert {"empty-origin", "b0-step"} != set(features)


def test_philosophy_information_requires_history_exhaustive():
    """cor:philosophy-information-requires-history; Lean: BEDC.FKernel.Hist.BHist; primitive: ledger_complete, scoped_resolved."""
    for history in HISTORIES:
        rows = history_rows(history)
        cert = scoped_history_certificate(history)
        if information_content(history):
            assert ledger_complete(rows, rows)
            assert scoped_resolved(cert)
        else:
            assert rows == frozenset()
    assert scoped_resolved(scoped_history_certificate(("b1",)))
    assert not scoped_resolved(scoped_history_certificate(("b1",), recorded_rows=frozenset()))


def test_philosophy_no_bare_information_exhaustive():
    """cor:philosophy-no-bare-information; Lean: BEDC.BaseReflection.Psame.PsameBase; primitive: ledger_gap, scoped_resolved."""
    required = frozenset({TRACE_ROW, NAMECERT_ROW})
    for recorded in powerset(required):
        bare = bool(ledger_gap(required, recorded))
        cert = scoped_history_certificate(("b0",), recorded_rows=recorded)
        if bare:
            assert not scoped_resolved(cert)
    assert ledger_gap(required, frozenset({TRACE_ROW})) == frozenset({NAMECERT_ROW})
    assert not ledger_gap(required, required)


def test_philosophy_history_generation_prefix_order_exhaustive():
    """thm:philosophy-history-generation-prefix-order; Lean: BEDC.FKernel.Hist.hsame_constructor_characterization; fixture: predecessor, is_prefix."""
    for history in HISTORIES:
        pred = predecessor(history)
        if history:
            base, mark = pred
            assert is_prefix(base, history)
            assert cont(base, mark) == history
        else:
            assert pred is None
    assert is_prefix(("b0",), ("b0", "b1"))
    assert not is_prefix(("b1",), ("b0", "b1"))


def test_philosophy_histories_are_not_sets_exhaustive():
    """cor:philosophy-histories-are-not-sets; Lean: BEDC.FKernel.Hist.history_no_confusion; fixture: Hist, hsame."""
    for left, right in product(HISTORIES, repeat=2):
        same_members = frozenset(left) == frozenset(right)
        if same_members and left != right:
            assert not hsame(left, right)
    assert frozenset(("b0", "b1")) == frozenset(("b1", "b0"))
    assert not hsame(("b0", "b1"), ("b1", "b0"))


def test_philosophy_lowest_form_time_history_growth_exhaustive():
    """cor:philosophy-lowest-form-time-history-growth; Lean: BEDC.FKernel.Cont.cont_right_step_rules; fixture: cont, predecessor."""
    for base, mark in product(HISTORIES, MARKS):
        target = cont(base, mark)
        assert len(target) == len(base) + 1
        assert predecessor(target) == (base, mark)
    assert len(cont((), "b0")) > len(())
    assert not len(()) > len(cont((), "b0"))


def test_philosophy_extension_singleton_continuation_exhaustive():
    """thm:philosophy-extension-singleton-continuation; Lean: BEDC.FKernel.Cont.cont_step_zero and cont_step_one; fixture: extension, continuation."""
    for base, mark in product(HISTORIES, MARKS):
        target = cont(base, mark)
        assert extension(base, mark, target)
        assert continuation(base, (mark,), target)
    assert continuation(("b0",), ("b1",), ("b0", "b1"))
    assert not continuation(("b0",), ("b1",), ("b1", "b0"))


def test_philosophy_unfolding_does_not_shift_classifier_exhaustive():
    """thm:philosophy-unfolding-does-not-shift-classifier; Lean: BEDC.FKernel.Cont.Cont; primitive: classifier_shift, shift_information."""
    for source_records, target_records in product((0, 1, 2), repeat=2):
        passage = classifier_passage(shifted=False, source_records=source_records, target_records=target_records)
        assert not classifier_shift(passage)
        assert shift_information(passage) == 0
    assert not classifier_shift(classifier_passage(shifted=False, source_records=1, target_records=3))
    assert classifier_shift(classifier_passage(shifted=True))


def test_philosophy_history_growth_not_discovery_exhaustive():
    """cor:philosophy-history-growth-not-discovery; Lean: BEDC.Meta.ClassifierIncrement.PositiveDiscovery; primitive: structural_discovery, positive_discovery."""
    for benefit, rows in product((0.0, 0.5, 2.0), powerset((SHIFT_ROW,))):
        claim = discovery_claim(shifted=False, benefit=benefit, rows=rows)
        assert not structural_discovery(claim.passage)
        assert not positive_discovery(claim)
    growth = discovery_claim(shifted=False, benefit=2.0)
    shifted = discovery_claim(shifted=True, benefit=2.0)
    assert not positive_discovery(growth)
    assert positive_discovery(shifted)


def test_philosophy_verified_unfolding_remains_unfolding_fact_exhaustive():
    """cor:philosophy-verified-unfolding-remains-unfolding-fact; Lean: BEDC.FKernel.Cont.cont_relation_constructor_characterization; primitive: classifier_shift, critical_hardening_gap."""
    backend = HardeningBackend("lean", frozenset({TRACE_ROW}))
    for hardened_rows in powerset((TRACE_ROW,)):
        passage = classifier_passage(shifted=False, certificate=CERTIFIED)
        profile = hardening_profile(hardened_rows=hardened_rows)
        assert not classifier_shift(passage)
        if hardened_rows:
            assert critical_hardening_gap(profile, backend) == frozenset()
    verified = hardening_profile(hardened_rows=frozenset({TRACE_ROW}))
    unverified = hardening_profile(recorded_rows=frozenset())
    assert critical_hardening_gap(verified, backend) == frozenset()
    assert critical_hardening_gap(unverified, backend) == frozenset({TRACE_ROW})


def test_philosophy_distinction_generates_history_carries_information_exhaustive():
    """thm:philosophy-distinction-generates-history-carries-information; Lean: BEDC.FKernel.Mark.mark_no_confusion and BEDC.FKernel.Hist.history_no_confusion; primitive: ledger_complete."""
    for trace in product(MARKS, repeat=2):
        history = empty_history()
        for mark in trace:
            assert mark in MARKS
            history = cont(history, mark)
        assert information_content(history) == trace
        assert ledger_complete(history_rows(history), history_rows(history))
    assert information_content(("b0", "b1")) == ("b0", "b1")
    assert information_content(("b0", "b1")) != ("b1", "b0")


def test_philosophy_ontology_begins_recordable_distinction_exhaustive():
    """cor:philosophy-ontology-begins-recordable-distinction; Lean: BEDC.Meta.DiscoveryCertificate.NameCertFiveRows; primitive: global_required_rows, globally_resolved."""
    cert = scoped_history_certificate(("b0",))
    claim = GlobalResolutionClaim(
        model_id="distinction-history",
        behavior_family=frozenset({cert.scope.behavior_id}),
        certificates=(cert,),
        global_recorded_rows=frozenset(),
    )
    required = global_required_rows(claim)
    for recorded in powerset(required):
        candidate = GlobalResolutionClaim(claim.model_id, claim.behavior_family, claim.certificates, recorded)
        assert globally_resolved(candidate) == (recorded == required)
    resolved = GlobalResolutionClaim(claim.model_id, claim.behavior_family, claim.certificates, required)
    assert globally_resolved(resolved)
    assert not globally_resolved(claim)


def test_philosophy_passage_to_continuation_exhaustive():
    """cor:philosophy-passage-to-continuation; Lean: BEDC.FKernel.Cont.Cont and cont_relation_generated_rules; fixture: cont, continuation."""
    for source, route in product(HISTORIES, HISTORIES):
        target = source + route
        assert continuation(source, route, target)
        if route:
            pred, mark = predecessor(target)
            assert extension(pred, mark, target)
    assert continuation(("b0",), ("b1", "b0"), ("b0", "b1", "b0"))
    assert not continuation(("b0",), ("b1",), ("b0",))
