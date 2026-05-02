import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuationMorphism_empty_source_tail_target_hsame {target : BHist}
    (m : ContinuationMorphism BHist.Empty target) : hsame m.tail target := by
  cases m with
  | mk tail rel =>
      exact hsame_symm (cont_left_unit_result rel)

theorem ContinuationMorphism_tail_empty_endpoint_hsame_iff {a b : BHist}
    (m : ContinuationMorphism a b) :
    hsame m.tail BHist.Empty ↔ hsame a b := by
  constructor
  · intro tailEmpty
    cases m with
    | mk tail rel =>
        cases tailEmpty
        exact hsame_symm (cont_deterministic rel (cont_right_unit a))
  · intro endpointSame
    cases m with
    | mk tail rel =>
        apply append_left_cancel (h := a)
        exact rel.symm.trans endpointSame.symm

end BEDC.Derived.CategoryUp
