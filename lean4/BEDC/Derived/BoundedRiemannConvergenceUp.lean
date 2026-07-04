import BEDC.FKernel.Cont
import BEDC.FKernel.Hist

namespace BEDC.Derived.BoundedRiemannConvergenceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

inductive BoundedRiemannConvergenceUp : Type where
  | mk
      (darbouxPartition regulatedFamily approachWindow taggedSum darbouxBracket uniformBound
        realEquality componentTransport replay provenance localName : BHist) :
      BoundedRiemannConvergenceUp
  deriving DecidableEq

def boundedRiemannConvergenceRows : BoundedRiemannConvergenceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedRiemannConvergenceUp.mk darbouX regulatedFamily approachWindow taggedSum
      darbouxBracket uniformBound realEquality componentTransport replay provenance localName =>
      [darbouX, regulatedFamily, approachWindow, taggedSum, darbouxBracket, uniformBound,
        realEquality, componentTransport, replay, provenance, localName]

theorem BoundedRiemannConvergenceCarrier_darboux_handoff
    (D F A T S B E H C P N : BHist) :
    boundedRiemannConvergenceRows (BoundedRiemannConvergenceUp.mk D F A T S B E H C P N) =
        [D, F, A, T, S, B, E, H, C, P, N] ∧
      hsame D D ∧ hsame F F ∧
        Cont F A (append F A) ∧ Cont T S (append T S) ∧
          Cont S B (append S B) ∧ Cont B E (append B E) := by
  -- BEDC touchpoint anchor: BHist BMark hsame Cont
  constructor
  · rfl
  · constructor
    · exact hsame_refl D
    · constructor
      · exact hsame_refl F
      · constructor
        · exact cont_intro rfl
        · constructor
          · exact cont_intro rfl
          · constructor
            · exact cont_intro rfl
            · exact cont_intro rfl

end BEDC.Derived.BoundedRiemannConvergenceUp
