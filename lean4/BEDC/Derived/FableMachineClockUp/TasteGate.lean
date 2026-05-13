import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

/-!
# FableMachineClockUp TasteGate carrier.
-/

namespace BEDC.Derived.FableMachineClockUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Finite local-clock packet with the nine displayed BEDC rows. -/
inductive FableMachineClockUp : Type where
  | mk :
      (sourceHist stepLedger selectedMarks selectorWitnesses clockBoundary transport
        continuation provenance nameCert : BHist) →
      FableMachineClockUp
  deriving DecidableEq

def fableMachineClockEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fableMachineClockEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fableMachineClockEncodeBHist h

def fableMachineClockDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fableMachineClockDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fableMachineClockDecodeBHist tail)

private theorem fableMachineClockDecodeEncodeBHist :
    ∀ h : BHist, fableMachineClockDecodeBHist (fableMachineClockEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def fableMachineClockToEventFlow : FableMachineClockUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FableMachineClockUp.mk sourceHist stepLedger selectedMarks selectorWitnesses
      clockBoundary transport continuation provenance nameCert =>
      [[BMark.b0],
        fableMachineClockEncodeBHist sourceHist,
        [BMark.b1, BMark.b0],
        fableMachineClockEncodeBHist stepLedger,
        [BMark.b1, BMark.b1, BMark.b0],
        fableMachineClockEncodeBHist selectedMarks,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fableMachineClockEncodeBHist selectorWitnesses,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fableMachineClockEncodeBHist clockBoundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fableMachineClockEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fableMachineClockEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        fableMachineClockEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        fableMachineClockEncodeBHist nameCert]

def fableMachineClockFromEventFlow : EventFlow → Option FableMachineClockUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | sourceHist :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | stepLedger :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | selectedMarks :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | selectorWitnesses :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | clockBoundary :: rest9 =>
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
                                                                      | nameCert ::
                                                                          rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] =>
                                                                              some
                                                                                (FableMachineClockUp.mk
                                                                                  (fableMachineClockDecodeBHist
                                                                                    sourceHist)
                                                                                  (fableMachineClockDecodeBHist
                                                                                    stepLedger)
                                                                                  (fableMachineClockDecodeBHist
                                                                                    selectedMarks)
                                                                                  (fableMachineClockDecodeBHist
                                                                                    selectorWitnesses)
                                                                                  (fableMachineClockDecodeBHist
                                                                                    clockBoundary)
                                                                                  (fableMachineClockDecodeBHist
                                                                                    transport)
                                                                                  (fableMachineClockDecodeBHist
                                                                                    continuation)
                                                                                  (fableMachineClockDecodeBHist
                                                                                    provenance)
                                                                                  (fableMachineClockDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ =>
                                                                              none

private theorem fableMachineClockRoundTrip :
    ∀ x : FableMachineClockUp,
      fableMachineClockFromEventFlow (fableMachineClockToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceHist stepLedger selectedMarks selectorWitnesses clockBoundary transport
      continuation provenance nameCert =>
      change
        some
          (FableMachineClockUp.mk
            (fableMachineClockDecodeBHist (fableMachineClockEncodeBHist sourceHist))
            (fableMachineClockDecodeBHist (fableMachineClockEncodeBHist stepLedger))
            (fableMachineClockDecodeBHist (fableMachineClockEncodeBHist selectedMarks))
            (fableMachineClockDecodeBHist (fableMachineClockEncodeBHist selectorWitnesses))
            (fableMachineClockDecodeBHist (fableMachineClockEncodeBHist clockBoundary))
            (fableMachineClockDecodeBHist (fableMachineClockEncodeBHist transport))
            (fableMachineClockDecodeBHist (fableMachineClockEncodeBHist continuation))
            (fableMachineClockDecodeBHist (fableMachineClockEncodeBHist provenance))
            (fableMachineClockDecodeBHist (fableMachineClockEncodeBHist nameCert))) =
          some
            (FableMachineClockUp.mk sourceHist stepLedger selectedMarks selectorWitnesses
              clockBoundary transport continuation provenance nameCert)
      rw [fableMachineClockDecodeEncodeBHist sourceHist,
        fableMachineClockDecodeEncodeBHist stepLedger,
        fableMachineClockDecodeEncodeBHist selectedMarks,
        fableMachineClockDecodeEncodeBHist selectorWitnesses,
        fableMachineClockDecodeEncodeBHist clockBoundary,
        fableMachineClockDecodeEncodeBHist transport,
        fableMachineClockDecodeEncodeBHist continuation,
        fableMachineClockDecodeEncodeBHist provenance,
        fableMachineClockDecodeEncodeBHist nameCert]

private theorem fableMachineClockToEventFlow_injective {x y : FableMachineClockUp} :
    fableMachineClockToEventFlow x = fableMachineClockToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fableMachineClockFromEventFlow (fableMachineClockToEventFlow x) =
        fableMachineClockFromEventFlow (fableMachineClockToEventFlow y) :=
    congrArg fableMachineClockFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fableMachineClockRoundTrip x).symm
      (Eq.trans hread (fableMachineClockRoundTrip y)))

instance fableMachineClockBHistCarrier : BHistCarrier FableMachineClockUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fableMachineClockToEventFlow
  fromEventFlow := fableMachineClockFromEventFlow

instance fableMachineClockChapterTasteGate : ChapterTasteGate FableMachineClockUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fableMachineClockFromEventFlow (fableMachineClockToEventFlow x) = some x
    exact fableMachineClockRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fableMachineClockToEventFlow_injective heq)

theorem FableMachineClockTasteGate_single_carrier_alignment :
    (∀ h : BHist, fableMachineClockDecodeBHist (fableMachineClockEncodeBHist h) = h) ∧
      (∀ x : FableMachineClockUp,
        fableMachineClockFromEventFlow (fableMachineClockToEventFlow x) = some x) ∧
        (∀ x y : FableMachineClockUp,
          fableMachineClockToEventFlow x = fableMachineClockToEventFlow y → x = y) ∧
          fableMachineClockEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact fableMachineClockDecodeEncodeBHist
  · constructor
    · exact fableMachineClockRoundTrip
    · constructor
      · intro x y heq
        exact fableMachineClockToEventFlow_injective heq
      · rfl

end BEDC.Derived.FableMachineClockUp
