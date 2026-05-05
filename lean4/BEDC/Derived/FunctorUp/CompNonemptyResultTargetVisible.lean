import BEDC.Derived.FunctorUp
import BEDC.Derived.CategoryUp.CompResultNonemptySourceTargetCases

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem FunctorPrefixHomCarrier_comp_nonempty_result_target_visible {p a b c f g k : BHist} :
    CategoryHomCarrier (append p a) (append p b) f ->
      CategoryHomCarrier (append p b) (append p c) g -> Cont f g (BHist.e1 k) ->
        ∃ r : BHist, append p c = BHist.e1 r ∧ UnaryHistory k ∧ UnaryHistory r ∧
          Cont (append p a) (BHist.e1 k) (BHist.e1 r) := by
  intro left right comp
  have casesData :=
    CategoryHomCarrier_comp_result_nonempty_source_target_cases left right comp
      (fun sameEmpty => not_hsame_e1_empty sameEmpty)
  cases casesData with
  | inl emptySource =>
      cases emptySource.right with
      | intro k' targetData =>
          cases targetData with
          | intro r data =>
              cases data.left
              exact Exists.intro r data.right
  | inr visibleSource =>
      cases visibleSource with
      | intro s sourceData =>
          cases sourceData with
          | intro k' targetData =>
              cases targetData with
              | intro r data =>
                  cases data.right.left
                  have sourceSame : hsame (BHist.e1 s) (append p a) := by
                    exact data.left.symm
                  have sourceRel : Cont (append p a) (BHist.e1 k) (BHist.e1 r) :=
                    cont_hsame_transport sourceSame (hsame_refl (BHist.e1 k))
                      (hsame_refl (BHist.e1 r)) data.right.right.right.right.right.right
                  exact Exists.intro r
                    (And.intro data.right.right.left
                      (And.intro data.right.right.right.right.left
                        (And.intro data.right.right.right.right.right.left sourceRel)))

theorem FunctorPrefixHomCarrier_comp_nonempty_result_source_target_cases
    {p a b c f g k : BHist} :
    CategoryHomCarrier (append p a) (append p b) f ->
      CategoryHomCarrier (append p b) (append p c) g -> Cont f g (BHist.e1 k) ->
        (hsame (append p a) BHist.Empty ∧ ∃ r : BHist, append p c = BHist.e1 r ∧
            UnaryHistory k ∧ UnaryHistory r ∧
              Cont (append p a) (BHist.e1 k) (BHist.e1 r)) ∨
          (∃ s r : BHist, append p a = BHist.e1 s ∧ append p c = BHist.e1 r ∧
            UnaryHistory s ∧ UnaryHistory k ∧ UnaryHistory r ∧
              Cont (BHist.e1 s) (BHist.e1 k) (BHist.e1 r)) := by
  intro left right comp
  have casesData :=
    CategoryHomCarrier_comp_result_nonempty_source_target_cases left right comp
      (fun sameEmpty => not_hsame_e1_empty sameEmpty)
  cases casesData with
  | inl emptySource =>
      left
      cases emptySource.right with
      | intro k' targetData =>
          cases targetData with
          | intro r data =>
              cases data.left
              exact And.intro emptySource.left (Exists.intro r data.right)
  | inr visibleSource =>
      right
      cases visibleSource with
      | intro s sourceData =>
          cases sourceData with
          | intro k' targetData =>
              cases targetData with
              | intro r data =>
                  cases data.right.left
                  exact Exists.intro s
                    (Exists.intro r
                      (And.intro data.left
                        (And.intro data.right.right.left
                          (And.intro data.right.right.right.left
                            (And.intro data.right.right.right.right.left
                              (And.intro data.right.right.right.right.right.left
                                data.right.right.right.right.right.right))))))

theorem FunctorPrefixHomCarrier_comp_nonempty_result_source_visible
    {p a b c f g k : BHist} :
    CategoryHomCarrier (append p a) (append p b) f ->
      CategoryHomCarrier (append p b) (append p c) g -> Cont f g (BHist.e1 k) ->
        (hsame (append p a) BHist.Empty -> False) ->
          ∃ s r : BHist, append p a = BHist.e1 s ∧ append p c = BHist.e1 r ∧
            UnaryHistory s ∧ UnaryHistory k ∧ UnaryHistory r ∧
              Cont (BHist.e1 s) (BHist.e1 k) (BHist.e1 r) := by
  intro left right comp sourceNonempty
  have casesData :=
    FunctorPrefixHomCarrier_comp_nonempty_result_source_target_cases left right comp
  cases casesData with
  | inl emptySource =>
      exact False.elim (sourceNonempty emptySource.left)
  | inr visibleSource =>
      exact visibleSource

theorem FunctorPrefixHomCarrier_comp_nonempty_result_target_component_e1_cases
    {p a b c f g k : BHist} :
    CategoryHomCarrier (append p a) (append p b) f ->
      CategoryHomCarrier (append p b) (append p c) g -> Cont f g (BHist.e1 k) ->
        (∃ p0 : BHist, p = BHist.e1 p0 ∧ UnaryHistory p0) ∨
          (∃ c0 : BHist, c = BHist.e1 c0 ∧ UnaryHistory c0) := by
  intro left right comp
  have visibleTarget :=
    FunctorPrefixHomCarrier_comp_nonempty_result_target_visible left right comp
  cases visibleTarget with
  | intro r data =>
      have targetEq : append p c = BHist.e1 r := data.left
      have appendTargetNonempty : hsame (append p c) BHist.Empty -> False := by
        intro targetEmpty
        exact not_hsame_e1_empty (targetEq.symm.trans targetEmpty)
      have componentCases :=
        Iff.mp (append_nonempty_iff (h := p) (k := c)) appendTargetNonempty
      cases componentCases with
      | inl prefixNonempty =>
          have prefixUnary : UnaryHistory p := unary_append_left_factor left.left
          exact Or.inl (unary_history_nonempty_e1_tail prefixUnary prefixNonempty)
      | inr targetNonempty =>
          have targetUnary : UnaryHistory c := unary_append_right_factor right.right.left
          exact Or.inr (unary_history_nonempty_e1_tail targetUnary targetNonempty)

theorem FunctorPrefixHomCarrier_comp_assoc_nonempty_result_target_component_e1_cases
    {p a b c d f g h fg gh left right k : BHist} :
    UnaryHistory p -> CategoryHomCarrier a b f -> CategoryHomCarrier b c g ->
      CategoryHomCarrier c d h -> Cont f g fg -> Cont g h gh -> Cont fg h left ->
        Cont f gh right -> hsame left (BHist.e1 k) ->
          (exists p0 : BHist, p = BHist.e1 p0 ∧ UnaryHistory p0) ∨
            (exists d0 : BHist, d = BHist.e1 d0 ∧ UnaryHistory d0) := by
  intro prefixCarrier first second third fgRel _ghRel leftRel _rightRel sameLeft
  have leftComposite : CategoryHomCarrier a c fg :=
    CategoryHomCarrier_comp_closed first second fgRel
  have prefixedLeft : CategoryHomCarrier (append p a) (append p c) fg :=
    FunctorPrefixHomCarrier_preserves prefixCarrier leftComposite
  have prefixedThird : CategoryHomCarrier (append p c) (append p d) h :=
    FunctorPrefixHomCarrier_preserves prefixCarrier third
  have visibleRel : Cont fg h (BHist.e1 k) :=
    cont_result_hsame_transport leftRel sameLeft
  exact
    FunctorPrefixHomCarrier_comp_nonempty_result_target_component_e1_cases
      prefixedLeft prefixedThird visibleRel

end BEDC.Derived.FunctorUp
