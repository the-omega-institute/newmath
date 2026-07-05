import BEDC.Derived.BoundedRiemannConvergenceUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow

namespace BEDC.Derived.BoundedRiemannConvergenceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow

def boundedRiemannConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedRiemannConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedRiemannConvergenceEncodeBHist h

def boundedRiemannConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedRiemannConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedRiemannConvergenceDecodeBHist tail)

private theorem BoundedRiemannConvergenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      boundedRiemannConvergenceDecodeBHist (boundedRiemannConvergenceEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedRiemannConvergenceToEventFlow :
    BoundedRiemannConvergenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (boundedRiemannConvergenceRows x).map boundedRiemannConvergenceEncodeBHist

theorem BoundedRiemannConvergenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        boundedRiemannConvergenceDecodeBHist (boundedRiemannConvergenceEncodeBHist h) = h) ∧
      (∀ D F A T S B E H C P N : BHist,
        boundedRiemannConvergenceRows (BoundedRiemannConvergenceUp.mk D F A T S B E H C P N) =
          [D, F, A, T, S, B, E, H, C, P, N] ∧
          Cont F A (append F A) ∧ Cont T S (append T S) ∧
            Cont S B (append S B) ∧ Cont B E (append B E)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont
  constructor
  · exact BoundedRiemannConvergenceTasteGate_single_carrier_alignment_decode_encode
  · intro D F A T S B E H C P N
    constructor
    · rfl
    · constructor
      · exact cont_intro rfl
      · constructor
        · exact cont_intro rfl
        · constructor
          · exact cont_intro rfl
          · exact cont_intro rfl

end BEDC.Derived.BoundedRiemannConvergenceUp
