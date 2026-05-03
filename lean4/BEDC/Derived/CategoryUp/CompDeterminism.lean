import BEDC.Derived.CategoryUp.TailCommClosed

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_comp_same_middle_factors_deterministic {a b c f g f' g' fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      CategoryHomCarrier a b f' -> CategoryHomCarrier b c g' -> Cont f' g' fg ->
        hsame f f' ∧ hsame g g' := by
  intro left _right comp left' _right' comp'
  have sameF : hsame f f' := CategoryHomCarrier_morphism_deterministic left left'
  have sameG : hsame g g' := by
    cases sameF
    exact cont_left_cancel comp comp'
  exact And.intro sameF sameG

theorem CategoryHomCarrier_comp_same_left_tail_factorization_deterministic
    {a b b' c c' f g g' fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      CategoryHomCarrier a b' f -> CategoryHomCarrier b' c' g' -> Cont f g' fg ->
        hsame b b' ∧ hsame g g' ∧ hsame c c' := by
  intro left right comp left' right' comp'
  have sameMiddle : hsame b b' :=
    CategoryHomCarrier_target_deterministic left left'
  have sameTail : hsame g g' :=
    cont_left_cancel comp comp'
  have transportedRight : CategoryHomCarrier b' c g' :=
    CategoryHomCarrier_hsame_transport sameMiddle (hsame_refl c) sameTail right
  have sameTarget : hsame c c' :=
    CategoryHomCarrier_target_deterministic transportedRight right'
  exact And.intro sameMiddle (And.intro sameTail sameTarget)

theorem CategoryHomCarrier_comp_same_right_tail_factorization_deterministic
    {a a' b b' c f f' g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      CategoryHomCarrier a' b' f' -> CategoryHomCarrier b' c g -> Cont f' g fg ->
        hsame b b' /\ hsame f f' /\ hsame a a' := by
  intro left right comp left' right' comp'
  have sameMiddle : hsame b b' :=
    CategoryHomCarrier_source_deterministic right right'
  have sameTail : hsame f f' :=
    cont_right_cancel comp comp'
  have transportedLeft : CategoryHomCarrier a' b f :=
    CategoryHomCarrier_hsame_transport
      (hsame_refl a') (hsame_symm sameMiddle) (hsame_symm sameTail) left'
  have sameSource : hsame a a' :=
    CategoryHomCarrier_source_deterministic left transportedLeft
  exact And.intro sameMiddle (And.intro sameTail sameSource)

theorem CategoryHomCarrier_comp_right_factor_endpoint_deterministic {a b b' c f g g' fg : BHist} :
    CategoryHomCarrier a b f -> Cont f g fg -> CategoryHomCarrier a c fg ->
      Cont f g' fg -> CategoryHomCarrier b' c g' -> hsame b b' ∧ hsame g g' := by
  intro left comp displayed comp' right'
  have right : CategoryHomCarrier b c g :=
    CategoryHomCarrier_comp_right_factor left comp displayed
  have sameG : hsame g g' := cont_left_cancel comp comp'
  have transportedRight : CategoryHomCarrier b c g' :=
    CategoryHomCarrier_hsame_transport (hsame_refl b) (hsame_refl c) sameG right
  have sameSource : hsame b b' :=
    CategoryHomCarrier_source_deterministic transportedRight right'
  exact And.intro sameSource sameG

theorem CategoryHomCarrier_comp_right_factor_target_deterministic {a b c c' f g g' fg : BHist} :
    CategoryHomCarrier a b f -> Cont f g fg -> CategoryHomCarrier a c fg ->
      Cont f g' fg -> CategoryHomCarrier b c' g' -> hsame c c' ∧ hsame g g' := by
  intro left comp displayed comp' right'
  have right : CategoryHomCarrier b c g :=
    CategoryHomCarrier_comp_right_factor left comp displayed
  have sameG : hsame g g' := cont_left_cancel comp comp'
  have transportedRight : CategoryHomCarrier b c g' :=
    CategoryHomCarrier_hsame_transport (hsame_refl b) (hsame_refl c) sameG right
  have sameTarget : hsame c c' :=
    CategoryHomCarrier_target_deterministic transportedRight right'
  exact And.intro sameTarget sameG

theorem CategoryHomCarrier_comp_left_factor_endpoint_deterministic {a b b' c f f' g fg : BHist} :
    CategoryHomCarrier b c g -> Cont f g fg -> CategoryHomCarrier a c fg ->
      Cont f' g fg -> CategoryHomCarrier a b' f' -> hsame b b' ∧ hsame f f' := by
  intro right comp displayed comp' left'
  have left : CategoryHomCarrier a b f :=
    CategoryHomCarrier_comp_left_factor right comp displayed
  have sameF : hsame f f' := cont_right_cancel comp comp'
  have transportedLeft : CategoryHomCarrier a b f' :=
    CategoryHomCarrier_hsame_transport (hsame_refl a) (hsame_refl b) sameF left
  have sameTarget : hsame b b' :=
    CategoryHomCarrier_target_deterministic transportedLeft left'
  exact And.intro sameTarget sameF

theorem CategoryHomCarrier_comp_result_hsame_congruence {a b c f g f' g' fg fg' : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      CategoryHomCarrier a b f' -> CategoryHomCarrier b c g' -> Cont f' g' fg' ->
        hsame fg fg' := by
  intro left right comp left' right' comp'
  have composite : CategoryHomCarrier a c fg :=
    CategoryHomCarrier_comp_closed left right comp
  have composite' : CategoryHomCarrier a c fg' :=
    CategoryHomCarrier_comp_closed left' right' comp'
  exact CategoryHomCarrier_morphism_deterministic composite composite'

theorem CategoryHomCarrier_comp_same_endpoints_result_deterministic
    {a b b' c f f' g g' fg fg' : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      CategoryHomCarrier a b' f' -> CategoryHomCarrier b' c g' -> Cont f' g' fg' ->
        hsame fg fg' := by
  intro left right comp left' right' comp'
  have composite : CategoryHomCarrier a c fg :=
    CategoryHomCarrier_comp_closed left right comp
  have composite' : CategoryHomCarrier a c fg' :=
    CategoryHomCarrier_comp_closed left' right' comp'
  exact CategoryHomCarrier_morphism_deterministic composite composite'

theorem CategoryHomCarrier_comp_factorization_iff {a c f g fg : BHist} :
    Cont f g fg ->
      (CategoryHomCarrier a c fg <->
        Exists (fun b : BHist => CategoryHomCarrier a b f ∧ CategoryHomCarrier b c g)) := by
  intro comp
  constructor
  · intro displayed
    have factors :
        CategoryHomCarrier a (append a f) f ∧ CategoryHomCarrier (append a f) c g :=
      (CategoryHomCarrier_comp_canonical_middle_iff
        (a := a) (c := c) (f := f) (g := g) (fg := fg) comp).mp displayed
    exact Exists.intro (append a f) factors
  · intro factorization
    cases factorization with
    | intro b factors =>
        exact CategoryHomCarrier_comp_closed factors.left factors.right comp

theorem CategoryHomCarrier_tail_comm_target_deterministic {a b c d f g fg gf : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg -> Cont g f gf ->
      CategoryHomCarrier a d gf -> hsame c d := by
  intro left right fgRel gfRel displayed
  have closed :=
    CategoryHomCarrier_tail_comm_closed left right fgRel gfRel
  exact CategoryHomCarrier_target_deterministic closed.right.left displayed

theorem CategoryHomCarrier_comp_left_factor_source_deterministic {a a' b c f f' g fg : BHist} :
    CategoryHomCarrier b c g -> Cont f g fg -> CategoryHomCarrier a c fg ->
      Cont f' g fg -> CategoryHomCarrier a' b f' -> hsame a a' ∧ hsame f f' := by
  intro right comp displayed comp' left'
  have left : CategoryHomCarrier a b f :=
    CategoryHomCarrier_comp_left_factor right comp displayed
  have sameF : hsame f f' := cont_right_cancel comp comp'
  have transportedLeft : CategoryHomCarrier a b f' :=
    CategoryHomCarrier_hsame_transport (hsame_refl a) (hsame_refl b) sameF left
  have sameSource : hsame a a' :=
    CategoryHomCarrier_source_deterministic transportedLeft left'
  exact And.intro sameSource sameF

theorem CategoryHomCarrier_unary_context_comp_middle_object_deterministic
    {p q a b b' c f g fg : BHist} :
    CategoryHomCarrier (append (append p a) q) (append (append p b) q) f ->
      CategoryHomCarrier (append (append p b') q) (append (append p c) q) g ->
        Cont f g fg ->
          CategoryHomCarrier (append (append p a) q) (append (append p c) q) fg ->
            hsame b b' := by
  intro left right comp displayed
  have leftSuff : CategoryHomCarrier (append p a) (append p b) f :=
    (CategoryHomCarrier_unary_suffix_iff.mp left).right
  have rightSuff : CategoryHomCarrier (append p b') (append p c) g :=
    (CategoryHomCarrier_unary_suffix_iff.mp right).right
  have displayedSuff : CategoryHomCarrier (append p a) (append p c) fg :=
    (CategoryHomCarrier_unary_suffix_iff.mp displayed).right
  have baseLeft : CategoryHomCarrier a b f :=
    And.intro (unary_append_right_factor leftSuff.left)
      (And.intro (unary_append_right_factor leftSuff.right.left)
        (And.intro leftSuff.right.right.left (cont_prefix_cancel leftSuff.right.right.right)))
  have baseRight : CategoryHomCarrier b' c g :=
    And.intro (unary_append_right_factor rightSuff.left)
      (And.intro (unary_append_right_factor rightSuff.right.left)
        (And.intro rightSuff.right.right.left (cont_prefix_cancel rightSuff.right.right.right)))
  have baseDisplayed : CategoryHomCarrier a c fg :=
    And.intro (unary_append_right_factor displayedSuff.left)
      (And.intro (unary_append_right_factor displayedSuff.right.left)
        (And.intro displayedSuff.right.right.left
          (cont_prefix_cancel displayedSuff.right.right.right)))
  exact CategoryHomCarrier_comp_middle_object_deterministic baseLeft baseRight comp baseDisplayed

theorem ContinuationMorphism_parallel_factor_comp_tail_middle_deterministic {a b b' c : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c)
    (left' : ContinuationMorphism a b') (right' : ContinuationMorphism b' c)
    (sameLeftTail : hsame left.tail left'.tail)
    (sameRightTail : hsame right.tail right'.tail) :
    Cont a left.tail b ∧ Cont b right.tail c ∧ Cont a left'.tail b' ∧
      Cont b' right'.tail c ∧ hsame b b' ∧
        hsame (ContinuationMorphism_comp_closed left right).tail
          (ContinuationMorphism_comp_closed left' right').tail := by
  have sameMiddle : hsame b b' :=
    ContinuationMorphism_target_deterministic left left' sameLeftTail
  have sameCompositeTail :
      hsame (ContinuationMorphism_comp_closed left right).tail
        (ContinuationMorphism_comp_closed left' right').tail := by
    cases left with
    | mk leftTail leftRel =>
        cases right with
        | mk rightTail rightRel =>
            cases left' with
            | mk leftTail' leftRel' =>
                cases right' with
                | mk rightTail' rightRel' =>
                    cases sameLeftTail
                    cases sameRightTail
                    rfl
  exact ⟨left.rel, right.rel, left'.rel, right'.rel, sameMiddle, sameCompositeTail⟩

theorem CategoryHomCarrier_parallel_factor_comp_tail_middle_deterministic
    {a b b' c f f' g g' : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g ->
      CategoryHomCarrier a b' f' -> CategoryHomCarrier b' c g' ->
        hsame f f' -> hsame g g' ->
          Cont a f b ∧ Cont b g c ∧ Cont a f' b' ∧ Cont b' g' c ∧
            hsame b b' ∧ hsame (append f g) (append f' g') := by
  intro left right left' right' sameF sameG
  have sameMiddle : hsame b b' := by
    cases sameF
    exact CategoryHomCarrier_target_deterministic left left'
  have sameCompositeTail : hsame (append f g) (append f' g') := by
    cases sameF
    cases sameG
    rfl
  exact ⟨left.right.right.right, right.right.right.right, left'.right.right.right,
    right'.right.right.right, sameMiddle, sameCompositeTail⟩

end BEDC.Derived.CategoryUp
