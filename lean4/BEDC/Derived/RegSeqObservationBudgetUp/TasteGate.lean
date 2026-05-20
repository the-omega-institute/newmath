import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegSeqObservationBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegSeqObservationBudgetUp : Type where
  | mk :
      (window readback realBudget diagonal tolerance transport route provenance name : BHist) →
        RegSeqObservationBudgetUp
  deriving DecidableEq

def regSeqObservationBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regSeqObservationBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regSeqObservationBudgetEncodeBHist h

def regSeqObservationBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regSeqObservationBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regSeqObservationBudgetDecodeBHist tail)

private theorem regSeqObservationBudget_decode_encode_bhist :
    ∀ h : BHist,
      regSeqObservationBudgetDecodeBHist
        (regSeqObservationBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regSeqObservationBudgetToEventFlow :
    RegSeqObservationBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegSeqObservationBudgetUp.mk window readback realBudget diagonal tolerance transport route
      provenance name =>
      [[BMark.b0],
        regSeqObservationBudgetEncodeBHist window,
        [BMark.b1, BMark.b0],
        regSeqObservationBudgetEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b0],
        regSeqObservationBudgetEncodeBHist realBudget,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regSeqObservationBudgetEncodeBHist diagonal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regSeqObservationBudgetEncodeBHist tolerance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regSeqObservationBudgetEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regSeqObservationBudgetEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regSeqObservationBudgetEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regSeqObservationBudgetEncodeBHist name]

def regSeqObservationBudgetFromEventFlow :
    EventFlow → Option RegSeqObservationBudgetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | window :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | readback :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | realBudget :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | diagonal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | tolerance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | route :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (RegSeqObservationBudgetUp.mk
                                                                                  (regSeqObservationBudgetDecodeBHist
                                                                                    window)
                                                                                  (regSeqObservationBudgetDecodeBHist
                                                                                    readback)
                                                                                  (regSeqObservationBudgetDecodeBHist
                                                                                    realBudget)
                                                                                  (regSeqObservationBudgetDecodeBHist
                                                                                    diagonal)
                                                                                  (regSeqObservationBudgetDecodeBHist
                                                                                    tolerance)
                                                                                  (regSeqObservationBudgetDecodeBHist
                                                                                    transport)
                                                                                  (regSeqObservationBudgetDecodeBHist
                                                                                    route)
                                                                                  (regSeqObservationBudgetDecodeBHist
                                                                                    provenance)
                                                                                  (regSeqObservationBudgetDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem regSeqObservationBudget_round_trip :
    ∀ x : RegSeqObservationBudgetUp,
      regSeqObservationBudgetFromEventFlow
        (regSeqObservationBudgetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk window readback realBudget diagonal tolerance transport route provenance name =>
      change
        some
          (RegSeqObservationBudgetUp.mk
            (regSeqObservationBudgetDecodeBHist
              (regSeqObservationBudgetEncodeBHist window))
            (regSeqObservationBudgetDecodeBHist
              (regSeqObservationBudgetEncodeBHist readback))
            (regSeqObservationBudgetDecodeBHist
              (regSeqObservationBudgetEncodeBHist realBudget))
            (regSeqObservationBudgetDecodeBHist
              (regSeqObservationBudgetEncodeBHist diagonal))
            (regSeqObservationBudgetDecodeBHist
              (regSeqObservationBudgetEncodeBHist tolerance))
            (regSeqObservationBudgetDecodeBHist
              (regSeqObservationBudgetEncodeBHist transport))
            (regSeqObservationBudgetDecodeBHist
              (regSeqObservationBudgetEncodeBHist route))
            (regSeqObservationBudgetDecodeBHist
              (regSeqObservationBudgetEncodeBHist provenance))
            (regSeqObservationBudgetDecodeBHist
              (regSeqObservationBudgetEncodeBHist name))) =
          some
            (RegSeqObservationBudgetUp.mk window readback realBudget diagonal tolerance
              transport route provenance name)
      rw [regSeqObservationBudget_decode_encode_bhist window,
        regSeqObservationBudget_decode_encode_bhist readback,
        regSeqObservationBudget_decode_encode_bhist realBudget,
        regSeqObservationBudget_decode_encode_bhist diagonal,
        regSeqObservationBudget_decode_encode_bhist tolerance,
        regSeqObservationBudget_decode_encode_bhist transport,
        regSeqObservationBudget_decode_encode_bhist route,
        regSeqObservationBudget_decode_encode_bhist provenance,
        regSeqObservationBudget_decode_encode_bhist name]

private theorem regSeqObservationBudgetToEventFlow_injective
    {x y : RegSeqObservationBudgetUp} :
    regSeqObservationBudgetToEventFlow x =
      regSeqObservationBudgetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regSeqObservationBudgetFromEventFlow
          (regSeqObservationBudgetToEventFlow x) =
        regSeqObservationBudgetFromEventFlow
          (regSeqObservationBudgetToEventFlow y) :=
    congrArg regSeqObservationBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regSeqObservationBudget_round_trip x).symm
      (Eq.trans hread (regSeqObservationBudget_round_trip y)))

instance regSeqObservationBudgetBHistCarrier :
    BHistCarrier RegSeqObservationBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regSeqObservationBudgetToEventFlow
  fromEventFlow := regSeqObservationBudgetFromEventFlow

instance regSeqObservationBudgetChapterTasteGate :
    ChapterTasteGate RegSeqObservationBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regSeqObservationBudgetFromEventFlow
        (regSeqObservationBudgetToEventFlow x) = some x
    exact regSeqObservationBudget_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regSeqObservationBudgetToEventFlow_injective heq)

instance regSeqObservationBudgetNontrivial : Nontrivial RegSeqObservationBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegSeqObservationBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegSeqObservationBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

instance regSeqObservationBudgetFieldFaithful :
    FieldFaithful RegSeqObservationBudgetUp where
  fields
    | RegSeqObservationBudgetUp.mk window readback realBudget diagonal tolerance transport route
        provenance name =>
        [window, readback, realBudget, diagonal, tolerance, transport, route, provenance, name]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y hfields
    cases x with
    | mk window readback realBudget diagonal tolerance transport route provenance name =>
        cases y with
        | mk window' readback' realBudget' diagonal' tolerance' transport' route' provenance'
            name' =>
            cases hfields
            rfl

def taste_gate : ChapterTasteGate RegSeqObservationBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

theorem RegSeqObservationBudgetTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regSeqObservationBudgetDecodeBHist (regSeqObservationBudgetEncodeBHist h) = h) ∧
      (∀ x : RegSeqObservationBudgetUp,
        regSeqObservationBudgetFromEventFlow
          (regSeqObservationBudgetToEventFlow x) = some x) ∧
        (∀ x y : RegSeqObservationBudgetUp,
          regSeqObservationBudgetToEventFlow x =
            regSeqObservationBudgetToEventFlow y → x = y) ∧
          regSeqObservationBudgetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regSeqObservationBudget_decode_encode_bhist
  · constructor
    · exact regSeqObservationBudget_round_trip
    · constructor
      · intro x y heq
        exact regSeqObservationBudgetToEventFlow_injective heq
      · rfl

theorem RegSeqObservationBudgetUp_StdBridge (x : RegSeqObservationBudgetUp) :
    regSeqObservationBudgetFromEventFlow (regSeqObservationBudgetToEventFlow x) = some x ∧
      ∃ window readback realBudget diagonal tolerance transport route provenance name : BHist,
        x = RegSeqObservationBudgetUp.mk window readback realBudget diagonal tolerance transport
          route provenance name ∧
          regSeqObservationBudgetToEventFlow x =
            [[BMark.b0],
              regSeqObservationBudgetEncodeBHist window,
              [BMark.b1, BMark.b0],
              regSeqObservationBudgetEncodeBHist readback,
              [BMark.b1, BMark.b1, BMark.b0],
              regSeqObservationBudgetEncodeBHist realBudget,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              regSeqObservationBudgetEncodeBHist diagonal,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              regSeqObservationBudgetEncodeBHist tolerance,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              regSeqObservationBudgetEncodeBHist transport,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              regSeqObservationBudgetEncodeBHist route,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b0],
              regSeqObservationBudgetEncodeBHist provenance,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b0],
              regSeqObservationBudgetEncodeBHist name] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regSeqObservationBudget_round_trip x
  · cases x with
    | mk window readback realBudget diagonal tolerance transport route provenance name =>
        exact
          ⟨window, readback, realBudget, diagonal, tolerance, transport, route, provenance,
            name, rfl, rfl⟩

end BEDC.Derived.RegSeqObservationBudgetUp
