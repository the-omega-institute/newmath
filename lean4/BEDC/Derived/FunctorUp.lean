import BEDC.Derived.CategoryUp

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem FunctorPrefixHomCarrier_preserves {p a b f : BHist} :
    UnaryHistory p -> CategoryHomCarrier a b f ->
      CategoryHomCarrier (append p a) (append p b) f := by
  intro prefixCarrier homCarrier
  cases homCarrier with
  | intro sourceCarrier homRest =>
      cases homRest with
      | intro targetCarrier homRest =>
          cases homRest with
          | intro morphismCarrier homCont =>
              cases homCont
              exact
                And.intro
                  (unary_append_closed prefixCarrier sourceCarrier)
                  (And.intro
                    (unary_append_closed prefixCarrier
                      (unary_cont_closed sourceCarrier morphismCarrier (cont_intro rfl)))
                    (And.intro morphismCarrier
                      (cont_intro (append_assoc p a f).symm)))

theorem FunctorPrefixHomCarrier_reflects {p a b f : BHist} :
    CategoryHomCarrier (append p a) (append p b) f -> CategoryHomCarrier a b f := by
  intro homCarrier
  cases homCarrier with
  | intro sourceCarrier homRest =>
      cases homRest with
      | intro targetCarrier homRest =>
          cases homRest with
          | intro morphismCarrier homCont =>
              exact
                And.intro
                  (unary_append_right_factor sourceCarrier)
                  (And.intro
                    (unary_append_right_factor targetCarrier)
                    (And.intro morphismCarrier
                      (cont_prefix_cancel homCont)))

theorem FunctorPrefixHomCarrier_iff {p a b f : BHist} :
    CategoryHomCarrier (append p a) (append p b) f ↔
      UnaryHistory p ∧ CategoryHomCarrier a b f := by
  constructor
  · intro homCarrier
    cases homCarrier with
    | intro sourceCarrier homRest =>
        exact
          And.intro
            (unary_append_left_factor sourceCarrier)
            (FunctorPrefixHomCarrier_reflects (And.intro sourceCarrier homRest))
  · intro prefixed
    cases prefixed with
    | intro prefixCarrier homCarrier =>
        exact FunctorPrefixHomCarrier_preserves prefixCarrier homCarrier

theorem FunctorPrefixHomCarrier_identity_closed {p a id : BHist} :
    UnaryHistory p -> UnaryHistory a -> Cont BHist.Empty BHist.Empty id ->
      CategoryHomCarrier (append p a) (append p a) id := by
  intro prefixCarrier sourceCarrier idRel
  have idSame : hsame id BHist.Empty := cont_deterministic idRel (cont_right_unit BHist.Empty)
  cases idSame
  exact
    And.intro
        (unary_append_closed prefixCarrier sourceCarrier)
        (And.intro
          (unary_append_closed prefixCarrier sourceCarrier)
          (And.intro unary_empty (cont_right_unit (append p a))))

theorem FunctorPrefixHomCarrier_comp_preserves {p a b c f g fg : BHist} :
    UnaryHistory p -> CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      CategoryHomCarrier (append p a) (append p c) fg := by
  intro prefixCarrier left right comp
  exact
    FunctorPrefixHomCarrier_preserves prefixCarrier
      (CategoryHomCarrier_comp_closed left right comp)

theorem FunctorPrefixHomCarrier_tail_comm_closed {p a b c f g fg gf : BHist} :
    UnaryHistory p -> CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      Cont g f gf -> CategoryHomCarrier (append p a) (append p c) fg ∧ hsame fg gf := by
  intro prefixCarrier left right fgRel gfRel
  exact
    And.intro
      (FunctorPrefixHomCarrier_comp_preserves prefixCarrier left right fgRel)
      (CategoryHomCarrier_tail_comm_hsame left right fgRel gfRel)

theorem FunctorPrefixHomCarrier_comp_assoc_preserves
    {p a b c d f g h fg gh left right : BHist} :
    UnaryHistory p -> CategoryHomCarrier a b f -> CategoryHomCarrier b c g ->
      CategoryHomCarrier c d h -> Cont f g fg -> Cont g h gh -> Cont fg h left ->
        Cont f gh right ->
          CategoryHomCarrier (append p a) (append p d) left ∧
            CategoryHomCarrier (append p a) (append p d) right ∧ hsame left right := by
  intro prefixCarrier first second third fgRel ghRel leftRel rightRel
  have closed :=
    CategoryHomCarrier_comp_assoc_closed first second third fgRel ghRel leftRel rightRel
  cases closed with
  | intro leftCarrier rest =>
      cases rest with
      | intro rightCarrier same =>
          exact
            And.intro
              (FunctorPrefixHomCarrier_preserves prefixCarrier leftCarrier)
              (And.intro
                (FunctorPrefixHomCarrier_preserves prefixCarrier rightCarrier)
                same)

theorem FunctorPrefixHomCarrier_comp_assoc_reflects
    {p a b c d f g h fg gh left right : BHist} :
    CategoryHomCarrier (append p a) (append p b) f ->
      CategoryHomCarrier (append p b) (append p c) g ->
        CategoryHomCarrier (append p c) (append p d) h -> Cont f g fg -> Cont g h gh ->
          Cont fg h left -> Cont f gh right ->
            CategoryHomCarrier a d left ∧ CategoryHomCarrier a d right ∧ hsame left right := by
  intro first second third fgRel ghRel leftRel rightRel
  exact
    CategoryHomCarrier_comp_assoc_closed
      (FunctorPrefixHomCarrier_reflects first)
      (FunctorPrefixHomCarrier_reflects second)
      (FunctorPrefixHomCarrier_reflects third)
      fgRel ghRel leftRel rightRel

theorem FunctorPrefixHomCarrier_empty_identity_preserves {p a : BHist} :
    UnaryHistory p -> UnaryHistory a ->
      CategoryHomCarrier (append p a) (append p a) BHist.Empty := by
  intro prefixCarrier objectCarrier
  exact FunctorPrefixHomCarrier_preserves prefixCarrier
    (CategoryHomCarrier_empty_identity objectCarrier)

theorem FunctorPrefixHomCarrier_empty_identity_iff {p a b : BHist} :
    CategoryHomCarrier (append p a) (append p b) BHist.Empty ↔
      UnaryHistory (append p a) ∧ UnaryHistory (append p b) ∧ hsame a b := by
  constructor
  · intro homCarrier
    have exactIdentity :=
      Iff.mp CategoryHomCarrier_empty_identity_iff homCarrier
    cases exactIdentity with
    | intro sourceCarrier rest =>
        cases rest with
        | intro targetCarrier samePrefixed =>
            exact
              And.intro sourceCarrier
                (And.intro targetCarrier (append_left_cancel samePrefixed))
  · intro data
    cases data with
    | intro sourceCarrier rest =>
        cases rest with
        | intro targetCarrier sameTail =>
            have samePrefixed : hsame (append p a) (append p b) := by
              cases sameTail
              rfl
            exact
              Iff.mpr CategoryHomCarrier_empty_identity_iff
                (And.intro sourceCarrier (And.intro targetCarrier samePrefixed))

theorem FunctorPrefixHomCarrier_empty_target_components_iff {p a f : BHist} :
    CategoryHomCarrier (append p a) BHist.Empty f <->
      hsame p BHist.Empty /\ hsame a BHist.Empty /\ hsame f BHist.Empty := by
  constructor
  · intro homCarrier
    have targetParts :=
      (CategoryHomCarrier_empty_target_iff (a := append p a) (f := f)).mp homCarrier
    have prefixParts := append_eq_empty_iff.mp targetParts.left
    exact And.intro prefixParts.left (And.intro prefixParts.right targetParts.right)
  · intro parts
    cases parts with
    | intro sameP rest =>
        cases rest with
        | intro sameA sameF =>
            cases sameP
            cases sameA
            cases sameF
            exact And.intro unary_empty
              (And.intro unary_empty (And.intro unary_empty (cont_right_unit BHist.Empty)))

theorem FunctorPrefixHomCarrier_source_prefix_deterministic {p q a target f : BHist} :
    CategoryHomCarrier (append p a) target f →
      CategoryHomCarrier (append q a) target f → hsame p q := by
  intro left right
  have sameSource : hsame (append p a) (append q a) :=
    CategoryHomCarrier_source_deterministic left right
  exact append_right_cancel (k := a) sameSource

end BEDC.Derived.FunctorUp
