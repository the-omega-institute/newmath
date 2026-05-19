import BEDC.Derived.ApophaticGateQuestionUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ApophaticGateQuestionUp : Type where
  | mk
      (socket question refusal readback transport route provenance nameRow : BHist) :
      ApophaticGateQuestionUp
  deriving DecidableEq

def apophaticGateQuestionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: apophaticGateQuestionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: apophaticGateQuestionEncodeBHist h

def apophaticGateQuestionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (apophaticGateQuestionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (apophaticGateQuestionDecodeBHist tail)

private theorem apophaticGateQuestionDecode_encode_bhist :
    ∀ h : BHist,
      apophaticGateQuestionDecodeBHist (apophaticGateQuestionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem apophaticGateQuestion_mk_congr
    {socket socket' question question' refusal refusal' readback readback'
      transport transport' route route' provenance provenance' nameRow nameRow' : BHist}
    (hSocket : socket' = socket)
    (hQuestion : question' = question)
    (hRefusal : refusal' = refusal)
    (hReadback : readback' = readback)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hNameRow : nameRow' = nameRow) :
    ApophaticGateQuestionUp.mk socket' question' refusal' readback' transport' route'
        provenance' nameRow' =
      ApophaticGateQuestionUp.mk socket question refusal readback transport route provenance
        nameRow := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSocket
  cases hQuestion
  cases hRefusal
  cases hReadback
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hNameRow
  rfl

def apophaticGateQuestionToEventFlow : ApophaticGateQuestionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ApophaticGateQuestionUp.mk socket question refusal readback transport route provenance
      nameRow =>
      [[BMark.b0],
        apophaticGateQuestionEncodeBHist socket,
        [BMark.b1, BMark.b0],
        apophaticGateQuestionEncodeBHist question,
        [BMark.b1, BMark.b1, BMark.b0],
        apophaticGateQuestionEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        apophaticGateQuestionEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        apophaticGateQuestionEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        apophaticGateQuestionEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        apophaticGateQuestionEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        apophaticGateQuestionEncodeBHist nameRow]

def apophaticGateQuestionFromEventFlow : EventFlow → Option ApophaticGateQuestionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | socket :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | question :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | refusal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | readback :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | route :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | nameRow :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (ApophaticGateQuestionUp.mk
                                                                          (apophaticGateQuestionDecodeBHist socket)
                                                                          (apophaticGateQuestionDecodeBHist question)
                                                                          (apophaticGateQuestionDecodeBHist refusal)
                                                                          (apophaticGateQuestionDecodeBHist readback)
                                                                          (apophaticGateQuestionDecodeBHist transport)
                                                                          (apophaticGateQuestionDecodeBHist route)
                                                                          (apophaticGateQuestionDecodeBHist provenance)
                                                                          (apophaticGateQuestionDecodeBHist nameRow))
                                                                  | _ :: _ => none

private theorem apophaticGateQuestion_round_trip :
    ∀ x : ApophaticGateQuestionUp,
      apophaticGateQuestionFromEventFlow (apophaticGateQuestionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk socket question refusal readback transport route provenance nameRow =>
      change
        some
          (ApophaticGateQuestionUp.mk
            (apophaticGateQuestionDecodeBHist (apophaticGateQuestionEncodeBHist socket))
            (apophaticGateQuestionDecodeBHist
              (apophaticGateQuestionEncodeBHist question))
            (apophaticGateQuestionDecodeBHist
              (apophaticGateQuestionEncodeBHist refusal))
            (apophaticGateQuestionDecodeBHist
              (apophaticGateQuestionEncodeBHist readback))
            (apophaticGateQuestionDecodeBHist
              (apophaticGateQuestionEncodeBHist transport))
            (apophaticGateQuestionDecodeBHist (apophaticGateQuestionEncodeBHist route))
            (apophaticGateQuestionDecodeBHist
              (apophaticGateQuestionEncodeBHist provenance))
            (apophaticGateQuestionDecodeBHist
              (apophaticGateQuestionEncodeBHist nameRow))) =
          some
            (ApophaticGateQuestionUp.mk socket question refusal readback transport route
              provenance nameRow)
      exact
        congrArg some
          (apophaticGateQuestion_mk_congr
            (apophaticGateQuestionDecode_encode_bhist socket)
            (apophaticGateQuestionDecode_encode_bhist question)
            (apophaticGateQuestionDecode_encode_bhist refusal)
            (apophaticGateQuestionDecode_encode_bhist readback)
            (apophaticGateQuestionDecode_encode_bhist transport)
            (apophaticGateQuestionDecode_encode_bhist route)
            (apophaticGateQuestionDecode_encode_bhist provenance)
            (apophaticGateQuestionDecode_encode_bhist nameRow))

private theorem apophaticGateQuestionToEventFlow_injective
    {x y : ApophaticGateQuestionUp} :
    apophaticGateQuestionToEventFlow x = apophaticGateQuestionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      apophaticGateQuestionFromEventFlow (apophaticGateQuestionToEventFlow x) =
        apophaticGateQuestionFromEventFlow (apophaticGateQuestionToEventFlow y) :=
    congrArg apophaticGateQuestionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (apophaticGateQuestion_round_trip x).symm
      (Eq.trans hread (apophaticGateQuestion_round_trip y)))

instance apophaticGateQuestionBHistCarrier :
    BHistCarrier ApophaticGateQuestionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := apophaticGateQuestionToEventFlow
  fromEventFlow := apophaticGateQuestionFromEventFlow

instance apophaticGateQuestionChapterTasteGate :
    ChapterTasteGate ApophaticGateQuestionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      apophaticGateQuestionFromEventFlow (apophaticGateQuestionToEventFlow x) =
        some x
    exact apophaticGateQuestion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (apophaticGateQuestionToEventFlow_injective heq)

def apophaticGateQuestionFields : ApophaticGateQuestionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ApophaticGateQuestionUp.mk socket question refusal readback transport route provenance
      nameRow =>
      [socket, question, refusal, readback, transport, route, provenance, nameRow]

def apophaticGateQuestionNameRow : ApophaticGateQuestionUp → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ApophaticGateQuestionUp.mk _socket _question _refusal _readback _transport _route
      _provenance nameRow => nameRow

private theorem apophaticGateQuestion_fields_faithful :
    ∀ x y : ApophaticGateQuestionUp,
      apophaticGateQuestionFields x = apophaticGateQuestionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk socket question refusal readback transport route provenance nameRow =>
      cases y with
      | mk socket' question' refusal' readback' transport' route' provenance' nameRow' =>
          cases hfields
          rfl

instance apophaticGateQuestionFieldFaithful :
    FieldFaithful ApophaticGateQuestionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := apophaticGateQuestionFields
  field_faithful := apophaticGateQuestion_fields_faithful

instance apophaticGateQuestionNontrivial : Nontrivial ApophaticGateQuestionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ApophaticGateQuestionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ApophaticGateQuestionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ApophaticGateQuestionTasteGate_single_carrier_alignment :
    (∀ x : ApophaticGateQuestionUp,
      apophaticGateQuestionFromEventFlow (apophaticGateQuestionToEventFlow x) =
        some x) ∧
      (∀ x y : ApophaticGateQuestionUp,
        apophaticGateQuestionFields x = apophaticGateQuestionFields y → x = y) ∧
        (∃ x y : ApophaticGateQuestionUp,
          x ≠ y ∧ apophaticGateQuestionFields x ≠ apophaticGateQuestionFields y) ∧
          (∃ x : ApophaticGateQuestionUp,
            apophaticGateQuestionFields x =
              [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
                BHist.Empty, BHist.Empty, BHist.Empty]) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact apophaticGateQuestion_round_trip
  · constructor
    · exact apophaticGateQuestion_fields_faithful
    · constructor
      · exact
          Exists.intro
            (ApophaticGateQuestionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty)
            (Exists.intro
              (ApophaticGateQuestionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)
              (by
                constructor
                · intro h
                  cases h
                · intro h
                  cases h))
      · exact
          Exists.intro
            (ApophaticGateQuestionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty)
            rfl

theorem ApophaticGateQuestionTasteGate_namecert_row_lock :
    ∀ x : ApophaticGateQuestionUp,
      ∃ socket question refusal readback transport route provenance nameRow : BHist,
        apophaticGateQuestionFields x =
            [socket, question, refusal, readback, transport, route, provenance, nameRow] ∧
          apophaticGateQuestionNameRow x = nameRow ∧ hsame nameRow nameRow := by
  -- BEDC touchpoint anchor: BHist BMark hsame
  intro x
  cases x with
  | mk socket question refusal readback transport route provenance nameRow =>
      exact
        ⟨socket, question, refusal, readback, transport, route, provenance, nameRow,
          rfl, rfl, hsame_refl nameRow⟩

end BEDC.Derived.ApophaticGateQuestionUp
