import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuationMorphism_comp_source_empty_tail_target_iff {a b c : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) :
    hsame a BHist.Empty ↔ hsame (ContinuationMorphism_comp_closed left right).tail c := by
  constructor
  · intro sourceEmpty
    cases sourceEmpty
    exact hsame_symm (cont_left_unit_result (ContinuationMorphism_comp_closed left right).rel)
  · intro tailTarget
    have compRel : Cont a c c :=
      cont_hsame_transport (hsame_refl a) tailTarget (hsame_refl c)
        (ContinuationMorphism_comp_closed left right).rel
    exact cont_right_cancel compRel (cont_left_unit c)

end BEDC.Derived.CategoryUp
