import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuationMorphism_empty_target_inversion {source : BHist}
    (m : ContinuationMorphism source BHist.Empty) :
    hsame source BHist.Empty ∧ hsame m.tail BHist.Empty := by
  cases m with
  | mk tail rel =>
      exact cont_empty_result_inversion rel

theorem ContinuationMorphism_e0_source_tail_cases {a target : BHist}
    (m : ContinuationMorphism (BHist.e0 a) target) :
    (m.tail = BHist.Empty /\ target = BHist.e0 a) \/
      (exists k r : BHist, m.tail = BHist.e0 k /\ target = BHist.e0 r /\
        Cont (BHist.e0 a) k r) \/
      (exists k r : BHist, m.tail = BHist.e1 k /\ target = BHist.e1 r /\
        Cont (BHist.e0 a) k r) := by
  cases m with
  | mk tail rel =>
      cases tail with
      | Empty =>
          left
          constructor
          · rfl
          · cases rel
            rfl
      | e0 k =>
          right
          left
          have resultCases := cont_step_result_inversions.left rel
          cases resultCases with
          | intro r data =>
              exact Exists.intro k
                (Exists.intro r (And.intro rfl (And.intro data.left data.right)))
      | e1 k =>
          right
          right
          have resultCases := cont_step_result_inversions.right rel
          cases resultCases with
          | intro r data =>
              exact Exists.intro k
                (Exists.intro r (And.intro rfl (And.intro data.left data.right)))

theorem ContinuationMorphism_e1_source_tail_cases {a target : BHist}
    (m : ContinuationMorphism (BHist.e1 a) target) :
    (m.tail = BHist.Empty /\ target = BHist.e1 a) \/
      (exists k r : BHist, m.tail = BHist.e0 k /\ target = BHist.e0 r /\
        Cont (BHist.e1 a) k r) \/
      (exists k r : BHist, m.tail = BHist.e1 k /\ target = BHist.e1 r /\
        Cont (BHist.e1 a) k r) := by
  cases m with
  | mk tail rel =>
      cases tail with
      | Empty =>
          left
          constructor
          · rfl
          · cases rel
            rfl
      | e0 k =>
          right
          left
          have resultCases := cont_step_result_inversions.left rel
          cases resultCases with
          | intro r data =>
              exact Exists.intro k
                (Exists.intro r (And.intro rfl (And.intro data.left data.right)))
      | e1 k =>
          right
          right
          have resultCases := cont_step_result_inversions.right rel
          cases resultCases with
          | intro r data =>
              exact Exists.intro k
                (Exists.intro r (And.intro rfl (And.intro data.left data.right)))

theorem ContinuationMorphism_e1_source_e0_target_tail_cases {a r : BHist}
    (m : ContinuationMorphism (BHist.e1 a) (BHist.e0 r)) :
    Exists (fun k : BHist => hsame m.tail (BHist.e0 k) ∧ Cont (BHist.e1 a) k r) := by
  cases m with
  | mk tail rel =>
      cases tail with
      | Empty =>
          exact False.elim (not_hsame_e1_e0 rel.symm)
      | e0 k =>
          have resultCases := cont_step_result_inversions.left rel
          cases resultCases with
          | intro r0 data =>
              have sameR : r = r0 := BHist.e0.inj data.left
              cases sameR
              exact Exists.intro k (And.intro (hsame_refl (BHist.e0 k)) data.right)
      | e1 k =>
          have resultCases := cont_step_result_inversions.right rel
          cases resultCases with
          | intro r1 data =>
              exact False.elim (not_hsame_e0_e1 data.left)

end BEDC.Derived.CategoryUp
