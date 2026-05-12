import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FoldMomentKernelUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FoldMomentKernelUp : Type where
  | mk :
      (window foldSource fiberLedger momentIndex collisionCount transportRoutes
        continuationRoutes packageProvenance localNameCert : BHist) →
      FoldMomentKernelUp

private def encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: encodeBHist h
  | BHist.e1 h => BMark.b1 :: encodeBHist h

private def decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (decodeBHist tail)

private theorem decode_encode_bhist : ∀ h : BHist, decodeBHist (encodeBHist h) = h := by
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
      transportRoutes continuationRoutes packageProvenance localNameCert =>
      [[BMark.b0],
        encodeBHist window,
        [BMark.b1, BMark.b0],
        encodeBHist foldSource,
        [BMark.b1, BMark.b1, BMark.b0],
        encodeBHist fiberLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist momentIndex,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist collisionCount,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist transportRoutes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist continuationRoutes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        encodeBHist packageProvenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        encodeBHist localNameCert]

private def foldMomentKernelFromEventFlow : EventFlow → Option FoldMomentKernelUp
  -- BEDC touchpoint anchor: BHist BMark
  | [_tag0, window, _tag1, foldSource, _tag2, fiberLedger, _tag3, momentIndex,
      _tag4, collisionCount, _tag5, transportRoutes, _tag6, continuationRoutes,
      _tag7, packageProvenance, _tag8, localNameCert] =>
      some
        (FoldMomentKernelUp.mk
          (decodeBHist window)
          (decodeBHist foldSource)
          (decodeBHist fiberLedger)
          (decodeBHist momentIndex)
          (decodeBHist collisionCount)
          (decodeBHist transportRoutes)
          (decodeBHist continuationRoutes)
          (decodeBHist packageProvenance)
          (decodeBHist localNameCert))
  | _ => none

private theorem foldMomentKernel_round_trip :
    ∀ x : FoldMomentKernelUp,
      foldMomentKernelFromEventFlow (foldMomentKernelToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk window foldSource fiberLedger momentIndex collisionCount transportRoutes
      continuationRoutes packageProvenance localNameCert =>
      change
        some
          (FoldMomentKernelUp.mk
            (decodeBHist (encodeBHist window))
            (decodeBHist (encodeBHist foldSource))
            (decodeBHist (encodeBHist fiberLedger))
            (decodeBHist (encodeBHist momentIndex))
            (decodeBHist (encodeBHist collisionCount))
            (decodeBHist (encodeBHist transportRoutes))
            (decodeBHist (encodeBHist continuationRoutes))
            (decodeBHist (encodeBHist packageProvenance))
            (decodeBHist (encodeBHist localNameCert))) =
          some
            (FoldMomentKernelUp.mk window foldSource fiberLedger momentIndex collisionCount
              transportRoutes continuationRoutes packageProvenance localNameCert)
      rw [decode_encode_bhist window, decode_encode_bhist foldSource,
        decode_encode_bhist fiberLedger, decode_encode_bhist momentIndex,
        decode_encode_bhist collisionCount, decode_encode_bhist transportRoutes,
        decode_encode_bhist continuationRoutes, decode_encode_bhist packageProvenance,
        decode_encode_bhist localNameCert]

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

def taste_gate : ChapterTasteGate FoldMomentKernelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  foldMomentKernelChapterTasteGate

end BEDC.Derived.FoldMomentKernelUp
