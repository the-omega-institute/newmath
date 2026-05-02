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

theorem CategoryHomCarrier_empty_target_chain_inversion {a b f g : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b BHist.Empty g ->
      hsame a BHist.Empty ∧ hsame b BHist.Empty ∧ hsame f BHist.Empty ∧
        hsame g BHist.Empty := by
  intro left right
  have rightEmpty := CategoryHomCarrier_empty_target_iff.mp right
  have transportedLeft : CategoryHomCarrier a BHist.Empty f :=
    CategoryHomCarrier_hsame_transport (hsame_refl a) rightEmpty.left (hsame_refl f) left
  have leftEmpty := CategoryHomCarrier_empty_target_iff.mp transportedLeft
  exact ⟨leftEmpty.left, rightEmpty.left, leftEmpty.right, rightEmpty.right⟩

theorem ContinuationMorphism_visible_source_empty_target_absurd {a : BHist} :
    (ContinuationMorphism (BHist.e0 a) BHist.Empty -> False) ∧
      (ContinuationMorphism (BHist.e1 a) BHist.Empty -> False) := by
  constructor
  · intro morphism
    have sourceEmpty := (ContinuationMorphism_empty_target_inversion morphism).left
    cases sourceEmpty
  · intro morphism
    have sourceEmpty := (ContinuationMorphism_empty_target_inversion morphism).left
    cases sourceEmpty

theorem ContinuationMorphism_comp_empty_middle_inversion {a c : BHist}
    (left : ContinuationMorphism a BHist.Empty) (right : ContinuationMorphism BHist.Empty c) :
    hsame a BHist.Empty ∧ hsame left.tail BHist.Empty ∧ hsame right.tail c ∧
      hsame (ContinuationMorphism_comp_closed left right).tail c := by
  cases left with
  | mk leftTail leftRel =>
      cases right with
      | mk rightTail rightRel =>
          have leftParts := cont_empty_result_inversion leftRel
          have rightTailTarget : hsame rightTail c := hsame_symm (cont_left_unit_result rightRel)
          constructor
          · exact leftParts.left
          · constructor
            · exact leftParts.right
            · constructor
              · exact rightTailTarget
              · change hsame (append leftTail rightTail) c
                exact hsame_trans (by cases leftParts.right; exact append_empty_left rightTail)
                  rightTailTarget

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

theorem ContinuationMorphism_e1_source_e0_target_tail_not_empty {a r : BHist}
    (m : ContinuationMorphism (BHist.e1 a) (BHist.e0 r)) :
    hsame m.tail BHist.Empty -> False := by
  intro tailEmpty
  cases ContinuationMorphism_e1_source_e0_target_tail_cases m with
  | intro k exposed =>
      exact not_hsame_e0_empty (hsame_trans (hsame_symm exposed.left) tailEmpty)

theorem ContinuationMorphism_e0_source_e1_target_tail_cases {a r : BHist}
    (m : ContinuationMorphism (BHist.e0 a) (BHist.e1 r)) :
    Exists (fun k : BHist => hsame m.tail (BHist.e1 k) ∧ Cont (BHist.e0 a) k r) := by
  cases m with
  | mk tail rel =>
      cases tail with
      | Empty =>
          exact False.elim (not_hsame_e0_e1 rel.symm)
      | e0 k =>
          have resultCases := cont_step_result_inversions.left rel
          cases resultCases with
          | intro r0 data =>
              exact False.elim (not_hsame_e1_e0 data.left)
      | e1 k =>
          have resultCases := cont_step_result_inversions.right rel
          cases resultCases with
          | intro r1 data =>
              have sameR : r = r1 := BHist.e1.inj data.left
              cases sameR
              exact Exists.intro k (And.intro (hsame_refl (BHist.e1 k)) data.right)

theorem ContinuationMorphism_e0_source_e1_target_tail_not_empty {a r : BHist}
    (m : ContinuationMorphism (BHist.e0 a) (BHist.e1 r)) :
    hsame m.tail BHist.Empty -> False := by
  intro tailEmpty
  cases ContinuationMorphism_e0_source_e1_target_tail_cases m with
  | intro k exposed =>
      exact not_hsame_e1_empty (hsame_trans (hsame_symm exposed.left) tailEmpty)

theorem ContinuationMorphism_e0_source_e0_target_tail_cases {a r : BHist}
    (m : ContinuationMorphism (BHist.e0 a) (BHist.e0 r)) :
    (m.tail = BHist.Empty ∧ hsame a r) ∨
      (∃ k : BHist, m.tail = BHist.e0 k ∧ Cont (BHist.e0 a) k r) := by
  cases m with
  | mk tail rel =>
      cases tail with
      | Empty =>
          left
          exact And.intro rfl (BHist.e0.inj rel).symm
      | e0 k =>
          right
          exact Exists.intro k (And.intro rfl (BHist.e0.inj rel))
      | e1 k =>
          exact False.elim (not_hsame_e0_e1 rel)

theorem ContinuationMorphism_e0_source_e0_target_tail_e1_absurd {a r k : BHist}
    (m : ContinuationMorphism (BHist.e0 a) (BHist.e0 r)) :
    hsame m.tail (BHist.e1 k) -> False := by
  cases m with
  | mk tail rel =>
      intro tailOne
      cases tail with
      | Empty =>
          exact not_hsame_emp_e1 tailOne
      | e0 t =>
          exact not_hsame_e0_e1 tailOne
      | e1 t =>
          have resultCases := cont_step_result_inversions.right rel
          cases resultCases with
          | intro r1 data =>
              exact not_hsame_e0_e1 data.left

theorem ContinuationMorphism_e1_source_e1_target_tail_cases {a r : BHist}
    (m : ContinuationMorphism (BHist.e1 a) (BHist.e1 r)) :
    (hsame m.tail BHist.Empty ∧ hsame a r) ∨
      (∃ k : BHist, hsame m.tail (BHist.e1 k) ∧ Cont (BHist.e1 a) k r) := by
  cases m with
  | mk tail rel =>
      cases tail with
      | Empty =>
          cases rel
          left
          exact And.intro (hsame_refl BHist.Empty) (hsame_refl a)
      | e0 k =>
          have resultCases := cont_step_result_inversions.left rel
          cases resultCases with
          | intro r0 data =>
              exact False.elim (not_hsame_e1_e0 data.left)
      | e1 k =>
          have resultCases := cont_step_result_inversions.right rel
          cases resultCases with
          | intro r1 data =>
              have sameR : r = r1 := BHist.e1.inj data.left
              cases sameR
              right
              exact Exists.intro k (And.intro (hsame_refl (BHist.e1 k)) data.right)

theorem ContinuationMorphism_e1_source_e1_target_tail_e0_absurd {a r k : BHist}
    (m : ContinuationMorphism (BHist.e1 a) (BHist.e1 r)) :
    hsame m.tail (BHist.e0 k) -> False := by
  intro tailZero
  cases ContinuationMorphism_e1_source_e1_target_tail_cases m with
  | inl emptyCase =>
      exact not_hsame_emp_e0 (hsame_trans (hsame_symm emptyCase.left) tailZero)
  | inr visibleCase =>
      cases visibleCase with
      | intro t exposed =>
          exact not_hsame_e1_e0 (hsame_trans (hsame_symm exposed.left) tailZero)

end BEDC.Derived.CategoryUp
