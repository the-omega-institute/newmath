import BEDC.Derived.CategoryUp.EmptySourceTail

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuationMorphism_empty_source_e1_target_tail_iff {r k : BHist}
    (m : ContinuationMorphism BHist.Empty (BHist.e1 r)) :
    hsame m.tail (BHist.e1 k) ↔ hsame r k := by
  have tailTarget : hsame m.tail (BHist.e1 r) :=
    ContinuationMorphism_empty_source_tail_target_hsame m
  constructor
  · intro tailVisible
    exact hsame_e1_iff.mp (hsame_trans (hsame_symm tailTarget) tailVisible)
  · intro samePayload
    exact hsame_trans tailTarget (hsame_e1_congr samePayload)

theorem ContinuationMorphism_empty_source_e0_target_tail_iff {r k : BHist}
    (m : ContinuationMorphism BHist.Empty (BHist.e0 r)) :
    hsame m.tail (BHist.e0 k) ↔ hsame r k := by
  have tailTarget : hsame m.tail (BHist.e0 r) :=
    ContinuationMorphism_empty_source_tail_target_hsame m
  constructor
  · intro tailVisible
    exact hsame_e0_iff.mp (hsame_trans (hsame_symm tailTarget) tailVisible)
  · intro samePayload
    exact hsame_trans tailTarget (hsame_e0_congr samePayload)

end BEDC.Derived.CategoryUp
