import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ModulusContinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ModulusContinuityUp : Type where
  | mk :
      (graph sourceWindow modulusRow dyadicLedger readback targetSeal transport replay
        provenance nameCert : BHist) →
      ModulusContinuityUp
  deriving DecidableEq

def modulusContinuityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: modulusContinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: modulusContinuityEncodeBHist h

def modulusContinuityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (modulusContinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (modulusContinuityDecodeBHist tail)

private theorem modulusContinuity_decode_encode_bhist :
    ∀ h : BHist, modulusContinuityDecodeBHist (modulusContinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def modulusContinuityFields : ModulusContinuityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ModulusContinuityUp.mk graph sourceWindow modulusRow dyadicLedger readback targetSeal
      transport replay provenance nameCert =>
      [graph, sourceWindow, modulusRow, dyadicLedger, readback, targetSeal, transport, replay,
        provenance, nameCert]

def modulusContinuityToEventFlow : ModulusContinuityUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (modulusContinuityFields x).map modulusContinuityEncodeBHist

def modulusContinuityFromEventFlow : EventFlow → Option ModulusContinuityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | graph :: rest0 =>
      match rest0 with
      | [] => none
      | sourceWindow :: rest1 =>
          match rest1 with
          | [] => none
          | modulusRow :: rest2 =>
              match rest2 with
              | [] => none
              | dyadicLedger :: rest3 =>
                  match rest3 with
                  | [] => none
                  | readback :: rest4 =>
                      match rest4 with
                      | [] => none
                      | targetSeal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | replay :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | nameCert :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (ModulusContinuityUp.mk
                                                  (modulusContinuityDecodeBHist graph)
                                                  (modulusContinuityDecodeBHist sourceWindow)
                                                  (modulusContinuityDecodeBHist modulusRow)
                                                  (modulusContinuityDecodeBHist dyadicLedger)
                                                  (modulusContinuityDecodeBHist readback)
                                                  (modulusContinuityDecodeBHist targetSeal)
                                                  (modulusContinuityDecodeBHist transport)
                                                  (modulusContinuityDecodeBHist replay)
                                                  (modulusContinuityDecodeBHist provenance)
                                                  (modulusContinuityDecodeBHist nameCert))
                                          | _ :: _ => none

private theorem modulusContinuity_round_trip :
    ∀ x : ModulusContinuityUp,
      modulusContinuityFromEventFlow (modulusContinuityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk graph sourceWindow modulusRow dyadicLedger readback targetSeal transport replay provenance
      nameCert =>
      change
        some
          (ModulusContinuityUp.mk
            (modulusContinuityDecodeBHist (modulusContinuityEncodeBHist graph))
            (modulusContinuityDecodeBHist (modulusContinuityEncodeBHist sourceWindow))
            (modulusContinuityDecodeBHist (modulusContinuityEncodeBHist modulusRow))
            (modulusContinuityDecodeBHist (modulusContinuityEncodeBHist dyadicLedger))
            (modulusContinuityDecodeBHist (modulusContinuityEncodeBHist readback))
            (modulusContinuityDecodeBHist (modulusContinuityEncodeBHist targetSeal))
            (modulusContinuityDecodeBHist (modulusContinuityEncodeBHist transport))
            (modulusContinuityDecodeBHist (modulusContinuityEncodeBHist replay))
            (modulusContinuityDecodeBHist (modulusContinuityEncodeBHist provenance))
            (modulusContinuityDecodeBHist (modulusContinuityEncodeBHist nameCert))) =
          some
            (ModulusContinuityUp.mk graph sourceWindow modulusRow dyadicLedger readback targetSeal
              transport replay provenance nameCert)
      rw [modulusContinuity_decode_encode_bhist graph,
        modulusContinuity_decode_encode_bhist sourceWindow,
        modulusContinuity_decode_encode_bhist modulusRow,
        modulusContinuity_decode_encode_bhist dyadicLedger,
        modulusContinuity_decode_encode_bhist readback,
        modulusContinuity_decode_encode_bhist targetSeal,
        modulusContinuity_decode_encode_bhist transport,
        modulusContinuity_decode_encode_bhist replay,
        modulusContinuity_decode_encode_bhist provenance,
        modulusContinuity_decode_encode_bhist nameCert]

private theorem modulusContinuityToEventFlow_injective {x y : ModulusContinuityUp} :
    modulusContinuityToEventFlow x = modulusContinuityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = modulusContinuityFromEventFlow (modulusContinuityToEventFlow x) :=
        (modulusContinuity_round_trip x).symm
      _ = modulusContinuityFromEventFlow (modulusContinuityToEventFlow y) :=
        congrArg modulusContinuityFromEventFlow hxy
      _ = some y := modulusContinuity_round_trip y
  exact Option.some.inj optionEq

instance modulusContinuityBHistCarrier : BHistCarrier ModulusContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := modulusContinuityToEventFlow
  fromEventFlow := modulusContinuityFromEventFlow

instance modulusContinuityChapterTasteGate : ChapterTasteGate ModulusContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change modulusContinuityFromEventFlow (modulusContinuityToEventFlow x) = some x
    exact modulusContinuity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (modulusContinuityToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ModulusContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  modulusContinuityChapterTasteGate

theorem ModulusContinuityTasteGate_single_carrier_alignment :
    (∀ h : BHist, modulusContinuityDecodeBHist (modulusContinuityEncodeBHist h) = h) ∧
      (∀ x : ModulusContinuityUp,
        modulusContinuityFromEventFlow (modulusContinuityToEventFlow x) = some x) ∧
        (∀ x y : ModulusContinuityUp,
          modulusContinuityToEventFlow x = modulusContinuityToEventFlow y → x = y) ∧
          modulusContinuityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨modulusContinuity_decode_encode_bhist,
      modulusContinuity_round_trip,
      (by
        intro x y heq
        exact modulusContinuityToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ModulusContinuityUp
