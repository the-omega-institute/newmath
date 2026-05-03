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

theorem ContinuationMorphism_empty_target_nonempty_iff {source : BHist} :
    Nonempty (ContinuationMorphism source BHist.Empty) ↔ hsame source BHist.Empty := by
  constructor
  · intro witness
    cases witness with
    | intro morphism =>
        exact (ContinuationMorphism_empty_target_inversion morphism).left
  · intro sameSource
    exact Nonempty.intro
      { tail := BHist.Empty,
        rel := cont_result_hsame_transport (cont_right_unit source) sameSource }

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

theorem ContinuationMorphism_e1_source_e0_target_tail_core_deterministic {a r k l : BHist}
    (m n : ContinuationMorphism (BHist.e1 a) (BHist.e0 r)) :
    hsame m.tail (BHist.e0 k) -> hsame n.tail (BHist.e0 l) -> hsame k l := by
  intro sameM sameN
  exact hsame_e0_iff.mp
    (hsame_trans (hsame_symm sameM)
      (hsame_trans (ContinuationMorphism_tail_deterministic m n) sameN))

theorem ContinuationMorphism_e1_source_e0_target_tail_e1_absurd {a r k : BHist}
    (m : ContinuationMorphism (BHist.e1 a) (BHist.e0 r)) :
    hsame m.tail (BHist.e1 k) -> False := by
  intro tailOne
  cases ContinuationMorphism_e1_source_e0_target_tail_cases m with
  | intro t exposed =>
      exact not_hsame_e0_e1 (hsame_trans (hsame_symm exposed.left) tailOne)

theorem ContinuationMorphism_e1_source_e0_target_tail_e0_iff {a r k : BHist}
    (m : ContinuationMorphism (BHist.e1 a) (BHist.e0 r)) :
    hsame m.tail (BHist.e0 k) ↔ Cont (BHist.e1 a) k r := by
  constructor
  · intro tailZero
    cases m with
    | mk tail rel =>
        cases tail with
        | Empty =>
            exact False.elim (not_hsame_emp_e0 tailZero)
        | e0 t =>
            have sameTK : hsame t k := hsame_e0_iff.mp tailZero
            cases sameTK
            exact BHist.e0.inj rel
        | e1 t =>
            exact False.elim (not_hsame_e1_e0 tailZero)
  · intro tailCont
    let displayed : ContinuationMorphism (BHist.e1 a) (BHist.e0 r) :=
      { tail := BHist.e0 k, rel := cont_step_zero tailCont }
    change hsame m.tail displayed.tail
    exact ContinuationMorphism_tail_deterministic m displayed

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

theorem ContinuationMorphism_e0_source_e1_target_tail_core_deterministic {a r k l : BHist}
    (m n : ContinuationMorphism (BHist.e0 a) (BHist.e1 r)) :
    hsame m.tail (BHist.e1 k) -> hsame n.tail (BHist.e1 l) -> hsame k l := by
  intro sameM sameN
  exact hsame_e1_iff.mp
    (hsame_trans (hsame_symm sameM)
      (hsame_trans (ContinuationMorphism_tail_deterministic m n) sameN))

theorem ContinuationMorphism_e0_source_e1_target_tail_e0_absurd {a r k : BHist}
    (m : ContinuationMorphism (BHist.e0 a) (BHist.e1 r)) :
    hsame m.tail (BHist.e0 k) -> False := by
  intro tailZero
  cases ContinuationMorphism_e0_source_e1_target_tail_cases m with
  | intro t exposed =>
      exact not_hsame_e1_e0 (hsame_trans (hsame_symm exposed.left) tailZero)

theorem ContinuationMorphism_e0_source_e1_target_tail_e1_iff {a r k : BHist}
    (m : ContinuationMorphism (BHist.e0 a) (BHist.e1 r)) :
    hsame m.tail (BHist.e1 k) ↔ Cont (BHist.e0 a) k r := by
  constructor
  · intro tailOne
    cases m with
    | mk tail rel =>
        cases tail with
        | Empty =>
            exact False.elim (not_hsame_emp_e1 tailOne)
        | e0 t =>
            exact False.elim (not_hsame_e0_e1 tailOne)
        | e1 t =>
            have sameTK : hsame t k := hsame_e1_iff.mp tailOne
            cases sameTK
            exact BHist.e1.inj rel
  · intro tailCont
    let displayed : ContinuationMorphism (BHist.e0 a) (BHist.e1 r) :=
      { tail := BHist.e1 k, rel := cont_step_one tailCont }
    change hsame m.tail displayed.tail
    exact ContinuationMorphism_tail_deterministic m displayed

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

theorem ContinuationMorphism_e0_source_e0_target_nonempty_tail_cases {a r : BHist}
    (m : ContinuationMorphism (BHist.e0 a) (BHist.e0 r)) :
    (hsame m.tail BHist.Empty -> False) ->
      Exists (fun k : BHist => hsame m.tail (BHist.e0 k) ∧ Cont (BHist.e0 a) k r) := by
  intro nonempty
  cases ContinuationMorphism_e0_source_e0_target_tail_cases m with
  | inl emptyCase =>
      exact False.elim (nonempty emptyCase.left)
  | inr visibleCase =>
      cases visibleCase with
      | intro k data =>
          exact Exists.intro k (And.intro data.left data.right)

theorem ContinuationMorphism_e0_source_e0_target_tail_core_deterministic {a r k l : BHist}
    (m n : ContinuationMorphism (BHist.e0 a) (BHist.e0 r)) :
    hsame m.tail (BHist.e0 k) -> hsame n.tail (BHist.e0 l) -> hsame k l := by
  intro sameM sameN
  exact hsame_e0_iff.mp
    (hsame_trans (hsame_symm sameM)
      (hsame_trans (ContinuationMorphism_tail_deterministic m n) sameN))

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

theorem ContinuationMorphism_e0_source_e0_target_tail_e0_iff {a r k : BHist}
    (m : ContinuationMorphism (BHist.e0 a) (BHist.e0 r)) :
    hsame m.tail (BHist.e0 k) ↔ Cont (BHist.e0 a) k r := by
  constructor
  · intro tailZero
    cases ContinuationMorphism_e0_source_e0_target_tail_cases m with
    | inl emptyCase =>
        exact False.elim
          (not_hsame_emp_e0 (hsame_trans (hsame_symm emptyCase.left) tailZero))
    | inr visibleCase =>
        cases visibleCase with
        | intro t exposed =>
            have samePayload : hsame t k :=
              hsame_e0_iff.mp (hsame_trans (hsame_symm exposed.left) tailZero)
            exact cont_hsame_transport (hsame_refl (BHist.e0 a)) samePayload
              (hsame_refl r) exposed.right
  · intro continuation
    exact cont_left_cancel m.rel (cont_step_zero continuation)

theorem ContinuationMorphism_e0_source_e0_target_tail_empty_iff {a r : BHist}
    (m : ContinuationMorphism (BHist.e0 a) (BHist.e0 r)) :
    hsame m.tail BHist.Empty ↔ hsame a r := by
  constructor
  · intro tailEmpty
    cases ContinuationMorphism_e0_source_e0_target_tail_cases m with
    | inl emptyCase =>
        exact emptyCase.right
    | inr visibleCase =>
        cases visibleCase with
        | intro k exposed =>
            exact False.elim (not_hsame_emp_e0 (hsame_trans (hsame_symm tailEmpty) exposed.left))
  · intro sameEndpoint
    let displayed : ContinuationMorphism (BHist.e0 a) (BHist.e0 r) :=
      { tail := BHist.Empty
        rel := by
          cases sameEndpoint
          exact cont_right_unit (BHist.e0 a) }
    exact ContinuationMorphism_tail_deterministic m displayed

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

theorem ContinuationMorphism_e1_source_e1_target_nonempty_tail_cases {a r : BHist}
    (m : ContinuationMorphism (BHist.e1 a) (BHist.e1 r)) :
    (hsame m.tail BHist.Empty -> False) ->
      Exists (fun k : BHist => hsame m.tail (BHist.e1 k) ∧ Cont (BHist.e1 a) k r) := by
  intro nonempty
  cases m with
  | mk tail rel =>
      cases tail with
      | Empty =>
          exact False.elim (nonempty (hsame_refl BHist.Empty))
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

theorem ContinuationMorphism_e1_source_e1_target_tail_core_deterministic {a r k l : BHist}
    (m n : ContinuationMorphism (BHist.e1 a) (BHist.e1 r)) :
    hsame m.tail (BHist.e1 k) -> hsame n.tail (BHist.e1 l) -> hsame k l := by
  intro sameM sameN
  exact hsame_e1_iff.mp
    (hsame_trans (hsame_symm sameM)
      (hsame_trans (ContinuationMorphism_tail_deterministic m n) sameN))

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

theorem ContinuationMorphism_e1_source_e1_target_tail_e1_iff {a r k : BHist}
    (m : ContinuationMorphism (BHist.e1 a) (BHist.e1 r)) :
    hsame m.tail (BHist.e1 k) ↔ Cont (BHist.e1 a) k r := by
  constructor
  · intro tailOne
    cases ContinuationMorphism_e1_source_e1_target_tail_cases m with
    | inl emptyCase =>
        exact False.elim
          (not_hsame_emp_e1 (hsame_trans (hsame_symm emptyCase.left) tailOne))
    | inr visibleCase =>
        cases visibleCase with
        | intro t exposed =>
            have samePayload : hsame t k :=
              hsame_e1_iff.mp (hsame_trans (hsame_symm exposed.left) tailOne)
            exact cont_hsame_transport (hsame_refl (BHist.e1 a)) samePayload
              (hsame_refl r) exposed.right
  · intro continuation
    exact cont_left_cancel m.rel (cont_step_one continuation)

theorem ContinuationMorphism_e1_source_e1_target_tail_empty_iff {a r : BHist}
    (m : ContinuationMorphism (BHist.e1 a) (BHist.e1 r)) :
    hsame m.tail BHist.Empty ↔ hsame a r := by
  constructor
  · intro tailEmpty
    cases ContinuationMorphism_e1_source_e1_target_tail_cases m with
    | inl emptyCase =>
        exact emptyCase.right
    | inr visibleCase =>
        cases visibleCase with
        | intro k exposed =>
            exact False.elim (not_hsame_emp_e1 (hsame_trans (hsame_symm tailEmpty) exposed.left))
  · intro sameEndpoint
    let displayed : ContinuationMorphism (BHist.e1 a) (BHist.e1 r) :=
      { tail := BHist.Empty
        rel := by
          cases sameEndpoint
          exact cont_right_unit (BHist.e1 a) }
    exact ContinuationMorphism_tail_deterministic m displayed

end BEDC.Derived.CategoryUp
