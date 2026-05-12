import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

/-!
# FoldMomentKernelUp TasteGate carrier.
-/

namespace BEDC.Derived.FoldMomentKernelUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.MainTheorems
open BEDC.Meta.TasteGate

/-- Finite collision-moment kernel packet with the nine visible BEDC rows. -/
inductive FoldMomentKernelUp : Type where
  | mk :
      (window foldSource fiberLedger momentIndex collisionCount transport continuation
        provenance nameCert : BHist) →
      FoldMomentKernelUp
  deriving DecidableEq

private def foldMomentKernelEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: foldMomentKernelEncodeBHist h
  | BHist.e1 h => BMark.b1 :: foldMomentKernelEncodeBHist h

private def foldMomentKernelDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (foldMomentKernelDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (foldMomentKernelDecodeBHist tail)

private theorem foldMomentKernelDecodeEncodeBHist :
    ∀ h : BHist, foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def foldMomentKernelToEventFlow : FoldMomentKernelUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FoldMomentKernelUp.mk window foldSource fiberLedger momentIndex collisionCount
      transport continuation provenance nameCert =>
      [[BMark.b0],
        foldMomentKernelEncodeBHist window,
        [BMark.b1, BMark.b0],
        foldMomentKernelEncodeBHist foldSource,
        [BMark.b1, BMark.b1, BMark.b0],
        foldMomentKernelEncodeBHist fiberLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        foldMomentKernelEncodeBHist momentIndex,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        foldMomentKernelEncodeBHist collisionCount,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        foldMomentKernelEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        foldMomentKernelEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        foldMomentKernelEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        foldMomentKernelEncodeBHist nameCert]

def foldMomentKernelFromEventFlow : EventFlow → Option FoldMomentKernelUp
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
              | foldSource :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | fiberLedger :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | momentIndex :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | collisionCount :: rest9 =>
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
                                                                      | nameCert :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (FoldMomentKernelUp.mk
                                                                                  (foldMomentKernelDecodeBHist
                                                                                    window)
                                                                                  (foldMomentKernelDecodeBHist
                                                                                    foldSource)
                                                                                  (foldMomentKernelDecodeBHist
                                                                                    fiberLedger)
                                                                                  (foldMomentKernelDecodeBHist
                                                                                    momentIndex)
                                                                                  (foldMomentKernelDecodeBHist
                                                                                    collisionCount)
                                                                                  (foldMomentKernelDecodeBHist
                                                                                    transport)
                                                                                  (foldMomentKernelDecodeBHist
                                                                                    continuation)
                                                                                  (foldMomentKernelDecodeBHist
                                                                                    provenance)
                                                                                  (foldMomentKernelDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ => none

private theorem foldMomentKernel_round_trip :
    ∀ x : FoldMomentKernelUp,
      foldMomentKernelFromEventFlow (foldMomentKernelToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk window foldSource fiberLedger momentIndex collisionCount transport continuation
      provenance nameCert =>
      change
        some
          (FoldMomentKernelUp.mk
            (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist window))
            (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist foldSource))
            (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist fiberLedger))
            (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist momentIndex))
            (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist collisionCount))
            (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist transport))
            (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist continuation))
            (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist provenance))
            (foldMomentKernelDecodeBHist (foldMomentKernelEncodeBHist nameCert))) =
          some
            (FoldMomentKernelUp.mk window foldSource fiberLedger momentIndex collisionCount
              transport continuation provenance nameCert)
      rw [foldMomentKernelDecodeEncodeBHist window, foldMomentKernelDecodeEncodeBHist foldSource,
        foldMomentKernelDecodeEncodeBHist fiberLedger,
        foldMomentKernelDecodeEncodeBHist momentIndex,
        foldMomentKernelDecodeEncodeBHist collisionCount,
        foldMomentKernelDecodeEncodeBHist transport,
        foldMomentKernelDecodeEncodeBHist continuation,
        foldMomentKernelDecodeEncodeBHist provenance,
        foldMomentKernelDecodeEncodeBHist nameCert]

private theorem foldMomentKernelToEventFlow_injective {x y : FoldMomentKernelUp} :
    foldMomentKernelToEventFlow x = foldMomentKernelToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      foldMomentKernelFromEventFlow (foldMomentKernelToEventFlow x) =
        foldMomentKernelFromEventFlow (foldMomentKernelToEventFlow y) :=
    congrArg foldMomentKernelFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (foldMomentKernel_round_trip x).symm
      (Eq.trans hread (foldMomentKernel_round_trip y)))

instance foldMomentKernelBHistCarrier : BHistCarrier FoldMomentKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := foldMomentKernelToEventFlow
  fromEventFlow := foldMomentKernelFromEventFlow

instance foldMomentKernelChapterTasteGate : ChapterTasteGate FoldMomentKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change foldMomentKernelFromEventFlow (foldMomentKernelToEventFlow x) = some x
    exact foldMomentKernel_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (foldMomentKernelToEventFlow_injective heq)

theorem FoldMomentKernelUp_zero_window_packet :
    ∃ x : FoldMomentKernelUp,
      x =
          FoldMomentKernelUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty ∧
        BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  let x :=
    FoldMomentKernelUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty
  exact ⟨x, rfl, ChapterTasteGate.round_trip x⟩

/-- Public gate object for the finite fold-moment-kernel carrier. -/
def taste_gate : ChapterTasteGate FoldMomentKernelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  foldMomentKernelChapterTasteGate

theorem FoldMomentKernelTasteGate_visible_rows :
    (forall x : FoldMomentKernelUp,
      foldMomentKernelFromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
      (forall x y : FoldMomentKernelUp,
        BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y -> x = y) ∧
        (forall (x : FoldMomentKernelUp) w m, List.Mem w (BHistCarrier.toEventFlow x) ->
          List.Mem m w -> m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    change foldMomentKernelFromEventFlow (foldMomentKernelToEventFlow x) = some x
    exact foldMomentKernel_round_trip x
  · constructor
    · intro x y heq
      exact foldMomentKernelToEventFlow_injective heq
    · intro x w m hw hm
      exact event_flow_conservativity (S := BHistCarrier.toEventFlow x) hw hm

end BEDC.Derived.FoldMomentKernelUp
