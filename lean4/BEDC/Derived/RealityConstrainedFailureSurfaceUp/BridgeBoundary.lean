import BEDC.Derived.RealityConstrainedFailureSurfaceUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.RealityConstrainedFailureSurfaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

private theorem RealityConstrainedFailureSurfaceUp_StdBridge_decode_encode
    (h : BHist) :
    realityConstrainedFailureSurfaceDecodeBHist
        (realityConstrainedFailureSurfaceEncodeBHist h) =
      h := by
  -- BEDC touchpoint anchor: BHist BMark
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

theorem RealityConstrainedFailureSurfaceUp_StdBridge
    (x : RealityConstrainedFailureSurfaceUp) :
    ∃ O D K U L H C P N bridge : BHist,
      x = RealityConstrainedFailureSurfaceUp.mk O D K U L H C P N ∧
        Cont O D bridge ∧
          hsame bridge bridge ∧
            realityConstrainedFailureSurfaceFromEventFlow
                (realityConstrainedFailureSurfaceToEventFlow x) =
              some x := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  cases x with
  | mk O D K U L H C P N =>
      refine
        ⟨O, D, K, U, L, H, C, P, N, append O D, rfl, rfl, hsame_refl (append O D), ?_⟩
      change
        some
          (RealityConstrainedFailureSurfaceUp.mk
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist O))
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist D))
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist K))
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist U))
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist L))
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist H))
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist C))
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist P))
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist N))) =
          some (RealityConstrainedFailureSurfaceUp.mk O D K U L H C P N)
      rw [RealityConstrainedFailureSurfaceUp_StdBridge_decode_encode O,
        RealityConstrainedFailureSurfaceUp_StdBridge_decode_encode D,
        RealityConstrainedFailureSurfaceUp_StdBridge_decode_encode K,
        RealityConstrainedFailureSurfaceUp_StdBridge_decode_encode U,
        RealityConstrainedFailureSurfaceUp_StdBridge_decode_encode L,
        RealityConstrainedFailureSurfaceUp_StdBridge_decode_encode H,
        RealityConstrainedFailureSurfaceUp_StdBridge_decode_encode C,
        RealityConstrainedFailureSurfaceUp_StdBridge_decode_encode P,
        RealityConstrainedFailureSurfaceUp_StdBridge_decode_encode N]

end BEDC.Derived.RealityConstrainedFailureSurfaceUp
