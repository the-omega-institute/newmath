import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EulerMethodFiniteStepUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EulerMethodFiniteStepUp : Type where
  | mk :
      (ode vectorField stepLedger stateReadback dyadic transport continuation provenance
        name : BHist) →
      EulerMethodFiniteStepUp

def eulerMethodFiniteStepEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: eulerMethodFiniteStepEncodeBHist h
  | BHist.e1 h => BMark.b1 :: eulerMethodFiniteStepEncodeBHist h

def eulerMethodFiniteStepDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (eulerMethodFiniteStepDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (eulerMethodFiniteStepDecodeBHist tail)

private theorem eulerMethodFiniteStepDecode_encode_bhist :
    ∀ h : BHist, eulerMethodFiniteStepDecodeBHist
      (eulerMethodFiniteStepEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def eulerMethodFiniteStepToEventFlow : EulerMethodFiniteStepUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | EulerMethodFiniteStepUp.mk ode vectorField stepLedger stateReadback dyadic transport
      continuation provenance name =>
      [[BMark.b0],
        eulerMethodFiniteStepEncodeBHist ode,
        [BMark.b1, BMark.b0],
        eulerMethodFiniteStepEncodeBHist vectorField,
        [BMark.b1, BMark.b1, BMark.b0],
        eulerMethodFiniteStepEncodeBHist stepLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        eulerMethodFiniteStepEncodeBHist stateReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        eulerMethodFiniteStepEncodeBHist dyadic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        eulerMethodFiniteStepEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        eulerMethodFiniteStepEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        eulerMethodFiniteStepEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        eulerMethodFiniteStepEncodeBHist name]

def eulerMethodFiniteStepFromEventFlow : EventFlow → Option EulerMethodFiniteStepUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | ode :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | vectorField :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | stepLedger :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | stateReadback :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | dyadic :: rest9 =>
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
                                                      | continuation :: rest13 =>
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
                                                                                (EulerMethodFiniteStepUp.mk
                                                                                  (eulerMethodFiniteStepDecodeBHist ode)
                                                                                  (eulerMethodFiniteStepDecodeBHist vectorField)
                                                                                  (eulerMethodFiniteStepDecodeBHist stepLedger)
                                                                                  (eulerMethodFiniteStepDecodeBHist stateReadback)
                                                                                  (eulerMethodFiniteStepDecodeBHist dyadic)
                                                                                  (eulerMethodFiniteStepDecodeBHist transport)
                                                                                  (eulerMethodFiniteStepDecodeBHist continuation)
                                                                                  (eulerMethodFiniteStepDecodeBHist provenance)
                                                                                  (eulerMethodFiniteStepDecodeBHist name))
                                                                          | _ :: _ => none

private theorem eulerMethodFiniteStep_round_trip :
    ∀ x : EulerMethodFiniteStepUp,
      eulerMethodFiniteStepFromEventFlow (eulerMethodFiniteStepToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk ode vectorField stepLedger stateReadback dyadic transport continuation provenance
      name =>
      change
        some
            (EulerMethodFiniteStepUp.mk
              (eulerMethodFiniteStepDecodeBHist (eulerMethodFiniteStepEncodeBHist ode))
              (eulerMethodFiniteStepDecodeBHist
                (eulerMethodFiniteStepEncodeBHist vectorField))
              (eulerMethodFiniteStepDecodeBHist
                (eulerMethodFiniteStepEncodeBHist stepLedger))
              (eulerMethodFiniteStepDecodeBHist
                (eulerMethodFiniteStepEncodeBHist stateReadback))
              (eulerMethodFiniteStepDecodeBHist
                (eulerMethodFiniteStepEncodeBHist dyadic))
              (eulerMethodFiniteStepDecodeBHist
                (eulerMethodFiniteStepEncodeBHist transport))
              (eulerMethodFiniteStepDecodeBHist
                (eulerMethodFiniteStepEncodeBHist continuation))
              (eulerMethodFiniteStepDecodeBHist
                (eulerMethodFiniteStepEncodeBHist provenance))
              (eulerMethodFiniteStepDecodeBHist
                (eulerMethodFiniteStepEncodeBHist name))) =
          some
            (EulerMethodFiniteStepUp.mk ode vectorField stepLedger stateReadback dyadic
              transport continuation provenance name)
      rw [eulerMethodFiniteStepDecode_encode_bhist ode,
        eulerMethodFiniteStepDecode_encode_bhist vectorField,
        eulerMethodFiniteStepDecode_encode_bhist stepLedger,
        eulerMethodFiniteStepDecode_encode_bhist stateReadback,
        eulerMethodFiniteStepDecode_encode_bhist dyadic,
        eulerMethodFiniteStepDecode_encode_bhist transport,
        eulerMethodFiniteStepDecode_encode_bhist continuation,
        eulerMethodFiniteStepDecode_encode_bhist provenance,
        eulerMethodFiniteStepDecode_encode_bhist name]

private theorem eulerMethodFiniteStepToEventFlow_injective
    {x y : EulerMethodFiniteStepUp} :
    eulerMethodFiniteStepToEventFlow x = eulerMethodFiniteStepToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      eulerMethodFiniteStepFromEventFlow (eulerMethodFiniteStepToEventFlow x) =
        eulerMethodFiniteStepFromEventFlow (eulerMethodFiniteStepToEventFlow y) :=
    congrArg eulerMethodFiniteStepFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (eulerMethodFiniteStep_round_trip x).symm
      (Eq.trans hread (eulerMethodFiniteStep_round_trip y)))

instance eulerMethodFiniteStepBHistCarrier : BHistCarrier EulerMethodFiniteStepUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := eulerMethodFiniteStepToEventFlow
  fromEventFlow := eulerMethodFiniteStepFromEventFlow

instance eulerMethodFiniteStepChapterTasteGate :
    ChapterTasteGate EulerMethodFiniteStepUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change eulerMethodFiniteStepFromEventFlow (eulerMethodFiniteStepToEventFlow x) =
      some x
    exact eulerMethodFiniteStep_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (eulerMethodFiniteStepToEventFlow_injective heq)

theorem EulerMethodFiniteStepTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier EulerMethodFiniteStepUp) ∧
      Nonempty (ChapterTasteGate EulerMethodFiniteStepUp) ∧
        (∀ h : BHist,
          eulerMethodFiniteStepDecodeBHist (eulerMethodFiniteStepEncodeBHist h) = h) ∧
          (∀ x : EulerMethodFiniteStepUp,
            eulerMethodFiniteStepFromEventFlow (eulerMethodFiniteStepToEventFlow x) =
              some x) ∧
            eulerMethodFiniteStepEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨eulerMethodFiniteStepBHistCarrier⟩,
      ⟨eulerMethodFiniteStepChapterTasteGate⟩,
      eulerMethodFiniteStepDecode_encode_bhist,
      eulerMethodFiniteStep_round_trip,
      rfl⟩

end BEDC.Derived.EulerMethodFiniteStepUp
