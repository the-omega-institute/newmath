from itertools import combinations, product

from bedc_quality_lab.classifier_shift import (
    ClassifierPassage,
    ClassifierState,
    classifier_shift,
    shift_information,
    structural_discovery,
)
from bedc_quality_lab.discovery import DiscoveryClaim, certified_discovery, positive_discovery, protocol_complete
from bedc_quality_lab.hardening import (
    HardeningBackend,
    HardeningProfile,
    critical_hardening_gap,
    fully_hardened_classifier,
    ledger_only_classifier,
)
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


Hist = tuple[str, ...]
Distinction = str

DISTINCTIONS = ("zero", "one")
HISTORIES: tuple[Hist, ...] = ((), ("zero",), ("one",), ("zero", "one"))
OBSERVATION_LABEL = "observation"
SUBJECT_LABELS = frozenset({"Subject", "ObserverSubstance", "SelfEntity", "GlobalViewpoint", "AbsoluteNow"})

CERTIFIED = classifier_certificate({"linear_identifiability_r2": 0.95, "approx_identifiability_proxy": 0.90})
UNCERTIFIED = classifier_certificate({"linear_identifiability_r2": 0.10, "approx_identifiability_proxy": 0.10})
PAIR = ("left", "right")
SHIFT_ROW = LedgerRowKey("classifier", "left->right")
POLICY = frozenset({SHIFT_ROW})
BASE_RELATION = frozenset({("left", "left", "same"), ("left", "right", "near"), ("right", "right", "same")})
SHIFTED_RELATION = frozenset({("left", "left", "same"), ("left", "right", "far"), ("right", "right", "same")})


def powerset(values):
    values = tuple(values)
    for size in range(len(values) + 1):
        for members in combinations(values, size):
            yield frozenset(members)


def encode(history: Hist) -> str:
    return "empty" if not history else ".".join(history)


def cont(base: Hist, distinction: Distinction) -> Hist:
    return base + (distinction,)


def predecessor(target: Hist) -> tuple[Hist, Distinction] | None:
    if not target:
        return None
    return target[:-1], target[-1]


def hsame(left: Hist, right: Hist) -> bool:
    return left == right


def observation_rows(history: Hist, distinction: Distinction) -> frozenset[LedgerRowKey]:
    target = cont(history, distinction)
    return frozenset(
        {
            LedgerRowKey("history", encode(history)),
            LedgerRowKey("distinction", distinction),
            LedgerRowKey(OBSERVATION_LABEL, f"{encode(history)}:{distinction}->{encode(target)}"),
        }
    )


def observer_scope(history: Hist) -> Scope:
    return Scope(
        domain_ids=frozenset({encode(history)}),
        model_id="observer-history",
        admitted_family_id="hsame",
        behavior_id=encode(history),
    )


def scoped_certificate(
    history: Hist = ("zero",),
    *,
    certificate=CERTIFIED,
    recorded_rows: frozenset[LedgerRowKey] | None = None,
    boundary: frozenset[str] = frozenset({"outside-history"}),
) -> ScopedCertificate:
    scope = observer_scope(history)
    required = scope_rows(scope)
    return ScopedCertificate(
        scope=scope,
        classifier_id="hsame-classifier",
        namecert_id="history-namecert",
        required_rows=required,
        recorded_rows=required if recorded_rows is None else recorded_rows,
        certificate=certificate,
        not_claimed_boundary=boundary,
    )


def cross_history_certificate(
    left: Hist,
    right: Hist,
    relation_id: str,
    rows: frozenset[LedgerRowKey],
    *,
    certificate=CERTIFIED,
    boundary: frozenset[str] = frozenset({"no-global-clock"}),
) -> ScopedCertificate:
    scope = Scope(
        domain_ids=frozenset({encode(left), encode(right)}),
        model_id="cross-history",
        admitted_family_id="certified-comparison",
        behavior_id=relation_id,
    )
    relation_row = LedgerRowKey("inter-history", f"{encode(left)}:{relation_id}:{encode(right)}")
    required = scope_rows(scope) | frozenset({relation_row})
    return ScopedCertificate(
        scope=scope,
        classifier_id="cross-history-classifier",
        namecert_id="cross-history-namecert",
        required_rows=required,
        recorded_rows=rows,
        certificate=certificate,
        not_claimed_boundary=boundary,
    )


def classifier_state(*, shifted: bool, certificate=CERTIFIED, rows: frozenset[LedgerRowKey] = POLICY) -> ClassifierState:
    return ClassifierState(
        source_ids=frozenset({"left", "right"}),
        pattern_id="observation-subject-time",
        ledger_policy=rows,
        relation=SHIFTED_RELATION if shifted else BASE_RELATION,
        certificate=certificate,
        surface_used=frozenset({PAIR}),
    )


def classifier_passage(
    *,
    shifted: bool = True,
    certificate=CERTIFIED,
    rows: frozenset[LedgerRowKey] = POLICY,
) -> ClassifierPassage:
    return ClassifierPassage(
        source=classifier_state(shifted=False),
        target=classifier_state(shifted=shifted, certificate=certificate),
        recorded_rows=rows,
    )


def hardening_profile(
    *,
    certified=True,
    required_rows: frozenset[LedgerRowKey] = frozenset(),
    recorded_rows: frozenset[LedgerRowKey] = frozenset(),
    hardened_rows: frozenset[LedgerRowKey] = frozenset(),
    critical_rows: frozenset[LedgerRowKey] = frozenset(),
) -> HardeningProfile:
    return HardeningProfile(
        certificate=CERTIFIED if certified else UNCERTIFIED,
        mode_rows=frozenset(),
        declared_mode_rows=frozenset(),
        open_mode_rows=frozenset(),
        ledger_required_rows=required_rows,
        ledger_recorded_rows=recorded_rows,
        critical_rows=critical_rows,
        hardened_rows=hardened_rows,
        frontier_rows=frozenset(),
        non_hardenable_residue=frozenset(),
    )


def observation_claim(
    *,
    shifted: bool = True,
    certificate=CERTIFIED,
    passage_rows: frozenset[LedgerRowKey] = POLICY,
    claim_rows: frozenset[LedgerRowKey] = POLICY,
    required_rows: frozenset[LedgerRowKey] = POLICY,
    benefit: float = 1.0,
    score: float = 0.1,
    debt: float = 0.1,
    public: bool = True,
    scope_sealed: bool = True,
    boundary: frozenset[str] = frozenset({"outside-history"}),
    scoped_cert: ScopedCertificate | None = None,
) -> DiscoveryClaim:
    return DiscoveryClaim(
        passage=classifier_passage(shifted=shifted, certificate=certificate, rows=passage_rows),
        benefit_terms={"trace": benefit},
        score_terms={"classifier": score},
        debt_terms={"ledger": debt},
        ledger_required_rows=required_rows,
        ledger_recorded_rows=claim_rows,
        public_cost_protocol=public,
        scope_sealed=scope_sealed,
        not_claimed_boundary=boundary,
        scoped_certificate=scoped_certificate() if scoped_cert is None else scoped_cert,
        black_box_debt_reduction=0.4,
        black_box_score_cost=0.1,
    )


def subject_free_signature(fields: frozenset[str]) -> bool:
    return fields.isdisjoint(SUBJECT_LABELS)


def same_act_shape(history: Hist, distinction: Distinction) -> dict[str, object]:
    target = cont(history, distinction)
    return {
        "observation": (history, distinction, target),
        "distinction": (history, distinction, target),
        "time": (history, distinction, target),
    }


def local_time_stream(history: Hist) -> tuple[tuple[Hist, Distinction, Hist], ...]:
    stream = []
    base: Hist = ()
    for distinction in history:
        target = cont(base, distinction)
        stream.append((base, distinction, target))
        base = target
    return tuple(stream)


def test_philosophy_observation_is_continuation_exhaustive():
    """thm:philosophy-observation-is-continuation; Lean: BEDC.FKernel.Cont.Cont and BEDC.FKernel.Cont.extension_as_singleton_continuation; primitive: ledger_complete."""
    for history, distinction in product(HISTORIES, DISTINCTIONS):
        target = cont(history, distinction)
        assert target == history + (distinction,)
        assert ledger_complete(observation_rows(history, distinction), observation_rows(history, distinction))
    positive = (("zero",), "one", ("zero", "one"))
    counter = (("zero",), "one", ("one", "zero"))
    assert cont(positive[0], positive[1]) == positive[2]
    assert cont(counter[0], counter[1]) != counter[2]


def test_philosophy_observation_needs_no_subject_substance_exhaustive():
    """cor:philosophy-observation-needs-no-subject-substance; Lean: BEDC.FKernel.Cont.Cont; primitive: scoped_resolved."""
    for fields in powerset(("Hist", "Distinction", "Target", "Subject", "ObserverSubstance")):
        cert = scoped_certificate(boundary=frozenset({"subject-free"}))
        if subject_free_signature(fields) and {"Hist", "Distinction", "Target"}.issubset(fields):
            assert scoped_resolved(cert)
        if not subject_free_signature(fields):
            assert "Subject" in fields or "ObserverSubstance" in fields
    assert subject_free_signature(frozenset({"Hist", "Distinction", "Target"}))
    assert not subject_free_signature(frozenset({"Hist", "Subject", "Target"}))


def test_philosophy_observation_ledger_event_exhaustive():
    """cor:philosophy-observation-ledger-event; Lean: BEDC.FKernel.Cont.cont_intro; primitive: ledger_gap, ledger_complete."""
    rows = observation_rows(("zero",), "one")
    for recorded in powerset(rows):
        complete = ledger_complete(rows, recorded)
        assert complete == (ledger_gap(rows, recorded) == frozenset())
    assert ledger_complete(rows, rows)
    assert not ledger_complete(rows, frozenset())


def test_philosophy_observer_identity_internal_exhaustive():
    """thm:philosophy-observer-identity-internal; Lean: BEDC.FKernel.Hist.hsame_iff_eq; primitive: scoped_resolved."""
    for history, certificate, boundary in product(HISTORIES, (CERTIFIED, UNCERTIFIED), (frozenset(), frozenset({"outside"}))):
        cert = scoped_certificate(history, certificate=certificate, boundary=boundary)
        assert scoped_resolved(cert) == (certificate["cert_status"] == "certified" and bool(boundary))
    assert scoped_resolved(scoped_certificate(("zero",)))
    assert not scoped_resolved(scoped_certificate(("zero",), certificate=UNCERTIFIED))


def test_philosophy_same_observer_not_mental_entity_exhaustive():
    """cor:philosophy-same-observer-not-mental-entity; Lean: BEDC.FKernel.Hist.hsame_constructor_inversion_full; primitive: classifier_certificate."""
    for left, right, mental in product(HISTORIES, HISTORIES, ("same-mind", "different-mind")):
        if hsame(left, right):
            assert hsame(left, right) is True
        else:
            assert hsame(left, right) is False
        assert classifier_certificate({"linear_identifiability_r2": 0.95, "approx_identifiability_proxy": 0.90})["cert_status"] == "certified"
        assert mental in {"same-mind", "different-mind"}
    assert hsame(("zero",), ("zero",))
    assert not hsame(("zero",), ("one",))


def test_philosophy_observer_identity_history_identity_exhaustive():
    """cor:philosophy-observer-identity-history-identity; Lean: BEDC.FKernel.Hist.history_sameness_equivalence; primitive: scoped_resolved."""
    for left, right in product(HISTORIES, HISTORIES):
        same = hsame(left, right)
        cert = scoped_certificate(left)
        if same:
            assert scoped_resolved(cert)
        else:
            assert not hsame(left, right)
    assert hsame(("zero", "one"), ("zero", "one"))
    assert not hsame(("zero", "one"), ("one", "zero"))


def test_philosophy_hsame_observer_identity_exhaustive():
    """thm:philosophy-hsame-observer-identity; Lean: BEDC.FKernel.Hist.hsame_e0_iff and BEDC.FKernel.Hist.hsame_e1_iff; primitive: ledger_complete."""
    for left, right, distinction in product(HISTORIES, HISTORIES, DISTINCTIONS):
        assert hsame(cont(left, distinction), cont(right, distinction)) == hsame(left, right)
    assert hsame(cont(("zero",), "one"), cont(("zero",), "one"))
    assert not hsame(cont(("zero",), "one"), cont(("one",), "one"))


def test_philosophy_no_subject_parameter_exhaustive():
    """thm:philosophy-no-subject-parameter; Lean: BEDC.FKernel.Cont.Cont; primitive: ledger_gap."""
    kernel_fields = frozenset({"history", "distinction", "successor"})
    for extra in powerset(("Subject", "GlobalViewpoint", "ledger")):
        fields = kernel_fields | extra
        gap = ledger_gap(kernel_fields, fields)
        assert not gap
        if fields & SUBJECT_LABELS:
            assert not subject_free_signature(fields)
    assert subject_free_signature(kernel_fields)
    assert not subject_free_signature(kernel_fields | frozenset({"Subject"}))


def test_philosophy_observer_is_history_exhaustive():
    """cor:philosophy-observer-is-history; Lean: BEDC.FKernel.Hist.BHist and BEDC.FKernel.Hist.hsame_refl; primitive: scope_rows."""
    for history in HISTORIES:
        rows = scope_rows(observer_scope(history))
        assert LedgerRowKey("source", f"observer-history:{encode(history)}") in rows
    assert hsame(("one",), ("one",))
    assert LedgerRowKey("source", "observer-history:outside") not in scope_rows(observer_scope(("one",)))


def test_philosophy_self_trace_reading_exhaustive():
    """cor:philosophy-self-trace-reading; Lean: BEDC.FKernel.Hist.hsame_trans; primitive: ledger_complete."""
    for history in HISTORIES:
        trace_rows = frozenset(LedgerRowKey("trace", f"{index}:{step}") for index, step in enumerate(history))
        assert ledger_complete(trace_rows, trace_rows)
    positive = frozenset({LedgerRowKey("trace", "0:zero")})
    assert ledger_complete(positive, positive)
    assert not ledger_complete(positive, frozenset())


def test_philosophy_no_substance_behind_trace_exhaustive():
    """cor:philosophy-no-substance-behind-trace; Lean: BEDC.FKernel.Hist.hsame_extension_self_absurd; primitive: critical_gap."""
    substance_row = LedgerRowKey("subject", "self-entity")
    trace_row = LedgerRowKey("trace", "0:zero")
    for entries in powerset((LedgerEntry(substance_row, "host", critical=True), LedgerEntry(trace_row, "kernel"))):
        gaps = tuple(entry for entry in entries if entry.critical)
        if gaps:
            assert critical_gap(gaps) == frozenset({substance_row})
    assert not critical_gap((LedgerEntry(trace_row, "kernel"),))
    assert critical_gap((LedgerEntry(substance_row, "host", critical=True),))


def test_philosophy_time_is_history_growth_exhaustive():
    """thm:philosophy-time-is-history-growth; Lean: BEDC.FKernel.Cont.extension_as_singleton_continuation; primitive: ledger_complete."""
    for history, distinction in product(HISTORIES, DISTINCTIONS):
        step = (history, distinction, cont(history, distinction))
        assert step in local_time_stream(cont(history, distinction))
    positive = local_time_stream(("zero", "one"))
    assert positive[-1] == (("zero",), "one", ("zero", "one"))
    assert (("one",), "zero", ("zero", "one")) not in positive


def test_philosophy_no_external_time_axis_exhaustive():
    """cor:philosophy-no-external-time-axis; Lean: BEDC.FKernel.Hist.BHist; primitive: ledger_gap."""
    history_rows = frozenset({LedgerRowKey("history", encode(("zero",)))})
    external_time = LedgerRowKey("time-axis", "absolute")
    for recorded in powerset((next(iter(history_rows)), external_time)):
        assert ledger_complete(history_rows, recorded) == (next(iter(history_rows)) in recorded)
    assert ledger_complete(history_rows, history_rows)
    assert not ledger_complete(history_rows | frozenset({external_time}), history_rows)


def test_philosophy_time_not_event_container_exhaustive():
    """cor:philosophy-time-not-event-container; Lean: BEDC.FKernel.Cont.cont_step_rules_pair; primitive: ledger_complete."""
    for history in HISTORIES:
        stream = local_time_stream(history)
        assert len(stream) == len(history)
        for base, distinction, target in stream:
            assert target == cont(base, distinction)
    assert local_time_stream(("zero",))[0] == ((), "zero", ("zero",))
    assert local_time_stream(()) == ()


def test_philosophy_continuation_time_asymmetric_exhaustive():
    """thm:philosophy-continuation-time-asymmetric; Lean: BEDC.FKernel.Cont.cont_step_result_inversions; primitive: classifier_shift."""
    for history, distinction in product(HISTORIES, DISTINCTIONS):
        target = cont(history, distinction)
        assert predecessor(target) == (history, distinction)
    assert cont(("zero",), "one") == ("zero", "one")
    assert predecessor(()) is None


def test_philosophy_time_arrow_not_physical_postulate_exhaustive():
    """cor:philosophy-time-arrow-not-physical-postulate; Lean: BEDC.FKernel.Cont.cont_step_zero_iff and cont_step_one_iff; primitive: ledger_complete."""
    for history, distinction in product(HISTORIES, DISTINCTIONS):
        forward = cont(history, distinction)
        assert predecessor(forward) == (history, distinction)
        assert ledger_complete(observation_rows(history, distinction), observation_rows(history, distinction))
    assert predecessor(("one",)) == ((), "one")
    assert predecessor(()) != ((), "zero")


def test_philosophy_past_readback_future_construction_exhaustive():
    """cor:philosophy-past-readback-future-construction; Lean: BEDC.FKernel.Cont.cont_result_e0_cases_iff and cont_result_e1_cases_iff; primitive: ledger_gap."""
    for history in HISTORIES:
        past = predecessor(history)
        if history:
            assert past is not None and cont(past[0], past[1]) == history
        else:
            assert past is None
    future = cont(("zero",), "one")
    assert future == ("zero", "one")
    assert predecessor(("zero", "one")) != (("one",), "zero")


def test_philosophy_no_kernel_global_clock_exhaustive():
    """thm:philosophy-no-kernel-global-clock; Lean: BEDC.FKernel.Hist.BHist; primitive: global_required_rows, globally_resolved."""
    cert = scoped_certificate(("zero",))
    claim = GlobalResolutionClaim("observer-history", frozenset({encode(("zero",))}), (cert,), frozenset())
    required = global_required_rows(claim)
    for recorded in powerset(required):
        candidate = GlobalResolutionClaim(claim.model_id, claim.behavior_family, claim.certificates, recorded)
        assert globally_resolved(candidate) == (recorded == required)
    assert globally_resolved(GlobalResolutionClaim(claim.model_id, claim.behavior_family, claim.certificates, required))
    assert not globally_resolved(claim)


def test_philosophy_no_absolute_present_exhaustive():
    """cor:philosophy-no-absolute-present; Lean: BEDC.FKernel.Hist.not_hsame_e0_e1; primitive: ledger_complete."""
    present_row = LedgerRowKey("present", "absolute-now")
    local_row = LedgerRowKey("history", encode(("zero",)))
    for recorded in powerset((local_row, present_row)):
        assert ledger_complete(frozenset({local_row}), recorded) == (local_row in recorded)
    assert ledger_complete(frozenset({local_row}), frozenset({local_row}))
    assert not ledger_complete(frozenset({present_row}), frozenset({local_row}))


def test_philosophy_cross_history_time_comparison_certified_exhaustive():
    """cor:philosophy-cross-history-time-comparison-certified; Lean: BEDC.FKernel.Hist.hsame_iff_eq; primitive: scoped_resolved."""
    base_cert = cross_history_certificate(("zero",), ("one",), "same-depth", frozenset())
    required = base_cert.required_rows
    for rows in powerset(required):
        cert = cross_history_certificate(("zero",), ("one",), "same-depth", rows)
        assert scoped_resolved(cert) == (rows == required)
    assert scoped_resolved(cross_history_certificate(("zero",), ("one",), "same-depth", required))
    assert not scoped_resolved(base_cert)


def test_philosophy_inter_history_relations_ledger_visible_exhaustive():
    """thm:philosophy-inter-history-relations-ledger-visible; Lean: BEDC.FKernel.Cont.cont_respects_hsame; primitive: structural_discovery, shift_information."""
    for shifted, certificate, rows in product((False, True), (UNCERTIFIED, CERTIFIED), powerset((SHIFT_ROW,))):
        passage = classifier_passage(shifted=shifted, certificate=certificate, rows=rows)
        if structural_discovery(passage):
            assert shift_information(passage) > 0
    assert structural_discovery(classifier_passage())
    assert not structural_discovery(classifier_passage(rows=frozenset()))


def test_philosophy_no_observer_outside_all_observers_exhaustive():
    """cor:philosophy-no-observer-outside-all-observers; Lean: BEDC.FKernel.Hist.BHist; primitive: scoped_resolved."""
    for fields in powerset(("Hist", "GlobalViewpoint", "AbsoluteNow")):
        if "Hist" in fields and subject_free_signature(fields):
            assert scoped_resolved(scoped_certificate())
        if "GlobalViewpoint" in fields or "AbsoluteNow" in fields:
            assert not subject_free_signature(fields)
    assert subject_free_signature(frozenset({"Hist"}))
    assert not subject_free_signature(frozenset({"GlobalViewpoint"}))


def test_philosophy_frame_independent_content_inter_history_invariant_exhaustive():
    """cor:philosophy-frame-independent-content-inter-history-invariant; Lean: BEDC.FKernel.Hist.hsame_equivalence; primitive: scoped_resolved."""
    for left, right in product(HISTORIES, HISTORIES):
        relation_id = "same-trace" if hsame(left, right) else "different-trace"
        cert = cross_history_certificate(left, right, relation_id, frozenset())
        full = cross_history_certificate(left, right, relation_id, cert.required_rows)
        assert scoped_resolved(full)
        assert not scoped_resolved(cert)
    assert hsame(("zero",), ("zero",))
    assert not hsame(("zero",), ("one",))


def test_philosophy_observation_distinction_time_identity_exhaustive():
    """thm:philosophy-observation-distinction-time-identity; Lean: BEDC.FKernel.Cont.extension_as_singleton_continuation; primitive: ledger_complete."""
    for history, distinction in product(HISTORIES, DISTINCTIONS):
        shape = same_act_shape(history, distinction)
        assert shape["observation"] == shape["distinction"] == shape["time"]
    assert len(set(same_act_shape(("zero",), "one").values())) == 1
    assert same_act_shape(("zero",), "one")["time"] != same_act_shape(("one",), "zero")["time"]


def test_philosophy_observation_not_added_after_distinction_exhaustive():
    """cor:philosophy-observation-not-added-after-distinction; Lean: BEDC.FKernel.Cont.cont_ext_right_step; primitive: ledger_gap."""
    for history, distinction in product(HISTORIES, DISTINCTIONS):
        rows = observation_rows(history, distinction)
        extra = LedgerRowKey("psychological-layer", f"{encode(history)}:{distinction}")
        assert ledger_complete(rows, rows | frozenset({extra}))
        assert not ledger_gap(rows, rows | frozenset({extra}))
    assert LedgerRowKey("psychological-layer", "empty:zero") not in observation_rows((), "zero")
    assert ledger_complete(observation_rows((), "zero"), observation_rows((), "zero"))


def test_philosophy_time_not_outside_observation_exhaustive():
    """cor:philosophy-time-not-outside-observation; Lean: BEDC.FKernel.Cont.cont_right_step_rules; primitive: ledger_complete."""
    for history, distinction in product(HISTORIES, DISTINCTIONS):
        time_row = LedgerRowKey("time", f"{encode(history)}:{distinction}")
        observation = observation_rows(history, distinction)
        recorded = observation | frozenset({time_row})
        assert ledger_complete(observation, recorded)
    assert cont((), "zero") == ("zero",)
    assert cont((), "zero") != ()


def test_philosophy_distinction_dynamic_exhaustive():
    """cor:philosophy-distinction-dynamic; Lean: BEDC.FKernel.Ext.Ext and BEDC.FKernel.Cont.extension_as_singleton_continuation; primitive: ledger_complete."""
    for history, distinction in product(HISTORIES, DISTINCTIONS):
        target = cont(history, distinction)
        assert len(target) == len(history) + 1
        assert predecessor(target) == (history, distinction)
    assert len(cont(("zero",), "one")) == 2
    assert len(("zero",)) != len(cont(("zero",), "one"))


def test_philosophy_continuation_universal_verb_exhaustive():
    """thm:philosophy-continuation-universal-verb; Lean: BEDC.Reflection.ComputationAsTrace_Statement and BEDC.FKernel.Cont.Cont; primitive: structural_discovery."""
    readings = ("action", "observation", "computation", "time")
    for reading, rows in product(readings, powerset((SHIFT_ROW,))):
        passage = classifier_passage(rows=rows)
        if structural_discovery(passage):
            assert reading in readings
    assert structural_discovery(classifier_passage())
    assert not structural_discovery(classifier_passage(shifted=False))


def test_philosophy_mathematical_structure_stabilized_continuation_exhaustive():
    """cor:philosophy-mathematical-structure-stabilized-continuation; Lean: BEDC.FKernel.Cont.append_assoc and BEDC.FKernel.Cont.cont_deterministic; primitive: ledger_only_classifier, fully_hardened_classifier."""
    stable_row = LedgerRowKey("stability", "continuation")
    backend = HardeningBackend("kernel", frozenset({stable_row}))
    for recorded in powerset((stable_row,)):
        profile = hardening_profile(required_rows=frozenset({stable_row}), recorded_rows=recorded)
        assert ledger_only_classifier(profile) == (recorded == frozenset({stable_row}))
    full = hardening_profile(required_rows=frozenset({stable_row}), recorded_rows=frozenset({stable_row}), critical_rows=frozenset({stable_row}))
    missing = hardening_profile(required_rows=frozenset({stable_row}), recorded_rows=frozenset(), critical_rows=frozenset({stable_row}))
    assert fully_hardened_classifier(full, backend)
    assert not fully_hardened_classifier(missing, backend)


def test_philosophy_action_observation_computation_time_cohere_exhaustive():
    """cor:philosophy-action-observation-computation-time-cohere; Lean: BEDC.FKernel.Cont.cont_step_rules_pair; primitive: classifier_shift, shift_information."""
    for history, distinction, reading in product(HISTORIES, DISTINCTIONS, ("action", "observation", "computation", "time")):
        shape = same_act_shape(history, distinction)
        assert shape["observation"] == shape["time"]
        assert reading in {"action", "observation", "computation", "time"}
    assert shift_information(classifier_passage()) == 1
    assert shift_information(classifier_passage(rows=frozenset())) == 0


def test_philosophy_observer_observation_time_synthesis_exhaustive():
    """thm:philosophy-observer-observation-time-synthesis; Lean: BEDC.FKernel.Hist.hsame_refl and BEDC.FKernel.Cont.Cont; primitive: positive_discovery."""
    for history, distinction in product(HISTORIES, DISTINCTIONS):
        target = cont(history, distinction)
        assert hsame(history, history)
        assert predecessor(target) == (history, distinction)
        assert same_act_shape(history, distinction)["observation"] == (history, distinction, target)
    positive = observation_claim()
    counter = observation_claim(shifted=False)
    assert positive_discovery(positive)
    assert not positive_discovery(counter)


def test_philosophy_excluded_subject_primitives_exhaustive():
    """cor:philosophy-excluded-subject-primitives; Lean: BEDC.FKernel.Hist.BHist and BEDC.FKernel.Cont.Cont; primitive: critical_hardening_gap."""
    excluded_row = LedgerRowKey("subject", "AbsoluteNow")
    backend = HardeningBackend("kernel", frozenset({excluded_row}))
    for hardened in powerset((excluded_row,)):
        profile = hardening_profile(critical_rows=frozenset({excluded_row}), hardened_rows=hardened)
        if excluded_row not in hardened:
            assert critical_hardening_gap(profile, backend) == frozenset({excluded_row})
    assert subject_free_signature(frozenset({"Hist", "Cont", "hsame"}))
    assert not subject_free_signature(frozenset({"Hist", "AbsoluteNow"}))


def test_philosophy_bedc_phenomenological_form_exhaustive():
    """cor:philosophy-bedc-phenomenological-form; Lean: BEDC.FKernel.Cont.extension_as_singleton_continuation and BEDC.FKernel.Hist.hsame_iff_eq; primitive: certified_discovery, protocol_complete."""
    for history, distinction, rows in product(HISTORIES, DISTINCTIONS, powerset((SHIFT_ROW,))):
        claim = observation_claim(passage_rows=rows, claim_rows=rows)
        if certified_discovery(claim):
            assert cont(history, distinction) == same_act_shape(history, distinction)["time"][2]
            assert protocol_complete(claim)
    positive = observation_claim()
    counter = observation_claim(passage_rows=frozenset(), claim_rows=frozenset())
    assert certified_discovery(positive) and protocol_complete(positive)
    assert not certified_discovery(counter)
