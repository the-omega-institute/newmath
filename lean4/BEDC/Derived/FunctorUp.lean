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

theorem FunctorPrefixHomCarrier_comp_right_factor {p a b c f g fg : BHist} :
    CategoryHomCarrier (append p a) (append p b) f -> Cont f g fg ->
      CategoryHomCarrier (append p a) (append p c) fg -> CategoryHomCarrier b c g := by
  intro left comp displayed
  exact FunctorPrefixHomCarrier_reflects
    (CategoryHomCarrier_comp_right_factor left comp displayed)

theorem FunctorPrefixHomCarrier_comp_left_factor {p a b c f g fg : BHist} :
    CategoryHomCarrier (append p b) (append p c) g -> Cont f g fg ->
      CategoryHomCarrier (append p a) (append p c) fg -> CategoryHomCarrier a b f := by
  intro right comp displayed
  exact FunctorPrefixHomCarrier_reflects
    (CategoryHomCarrier_comp_left_factor right comp displayed)

theorem FunctorPrefixHomCarrier_comp_left_factor_public_readback {p a b c f g fg : BHist} :
    CategoryHomCarrier (append p b) (append p c) g -> Cont f g fg ->
      CategoryHomCarrier (append p a) (append p c) fg ->
        CategoryHomCarrier a b f /\
          (forall {f' : BHist}, Cont f' g fg -> CategoryHomCarrier a b f' -> hsame f f') := by
  intro right comp displayed
  constructor
  · exact FunctorPrefixHomCarrier_comp_left_factor right comp displayed
  · intro f' comp' _left
    exact cont_right_cancel comp comp'

theorem FunctorPrefixHomCarrier_comp_public_readback {p a b c f g fg : BHist} :
    UnaryHistory p -> CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      CategoryHomCarrier (append p a) (append p c) fg ∧
        (forall {fg' : BHist}, CategoryHomCarrier (append p a) (append p c) fg' ->
          hsame fg fg') := by
  intro prefixCarrier left right comp
  have baseComposite : CategoryHomCarrier a c fg :=
    CategoryHomCarrier_comp_closed left right comp
  constructor
  · exact FunctorPrefixHomCarrier_preserves prefixCarrier baseComposite
  · intro fg' displayed
    exact
      CategoryHomCarrier_morphism_deterministic baseComposite
        (FunctorPrefixHomCarrier_reflects displayed)

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

theorem FunctorPrefixHomCarrier_e1_prefix_empty_identity_iff {p a b : BHist} :
    CategoryHomCarrier (append (BHist.e1 p) a) (append (BHist.e1 p) b) BHist.Empty ↔
      UnaryHistory p ∧ UnaryHistory a ∧ UnaryHistory b ∧ hsame a b := by
  constructor
  · intro homCarrier
    have identityData :=
      (FunctorPrefixHomCarrier_empty_identity_iff
        (p := BHist.e1 p) (a := a) (b := b)).mp homCarrier
    cases identityData with
    | intro sourceCarrier rest =>
        cases rest with
        | intro targetCarrier sameTail =>
            have sourceFactors :=
              (unary_append_factors_iff_result (h := BHist.e1 p) (k := a)).mpr
                sourceCarrier
            have targetFactors :=
              (unary_append_factors_iff_result (h := BHist.e1 p) (k := b)).mpr
                targetCarrier
            exact
              And.intro (unary_e1_inversion sourceFactors.left)
                (And.intro sourceFactors.right
                  (And.intro targetFactors.right sameTail))
  · intro data
    cases data with
    | intro prefixCarrier rest =>
        cases rest with
        | intro sourceCarrier rest =>
            cases rest with
            | intro targetCarrier sameTail =>
                exact
                  (FunctorPrefixHomCarrier_empty_identity_iff
                    (p := BHist.e1 p) (a := a) (b := b)).mpr
                    (And.intro
                      (unary_append_closed (unary_e1_closed prefixCarrier) sourceCarrier)
                      (And.intro
                        (unary_append_closed (unary_e1_closed prefixCarrier) targetCarrier)
                        sameTail))

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

theorem FunctorPrefixHomCarrier_empty_source_components_iff {p b f : BHist} :
    CategoryHomCarrier BHist.Empty (append p b) f <->
      UnaryHistory p ∧ UnaryHistory b ∧ hsame f (append p b) := by
  constructor
  · intro homCarrier
    have emptySourceData :=
      (CategoryHomCarrier_empty_source_iff (b := append p b) (f := f)).mp homCarrier
    exact
      And.intro
        (unary_append_left_factor emptySourceData.left)
        (And.intro (unary_append_right_factor emptySourceData.left) emptySourceData.right)
  · intro parts
    cases parts with
    | intro prefixCarrier rest =>
        cases rest with
        | intro targetCarrier sameMorphism =>
            exact
              (CategoryHomCarrier_empty_source_iff (b := append p b) (f := f)).mpr
                (And.intro (unary_append_closed prefixCarrier targetCarrier) sameMorphism)

theorem FunctorPrefixHomCarrier_e1_morphism_target_components_iff {p a k r : BHist} :
    CategoryHomCarrier (append p a) (BHist.e1 r) (BHist.e1 k) <->
      UnaryHistory p /\ UnaryHistory a /\ UnaryHistory k /\ Cont (append p a) k r := by
  constructor
  · intro homCarrier
    have data :=
      (CategoryHomCarrier_e1_morphism_target_iff (a := append p a) (k := k) (r := r)).mp
        homCarrier
    exact And.intro (unary_append_left_factor data.left)
      (And.intro (unary_append_right_factor data.left)
        (And.intro data.right.left data.right.right))
  · intro data
    exact
      (CategoryHomCarrier_e1_morphism_target_iff (a := append p a) (k := k) (r := r)).mpr
        (And.intro (unary_append_closed data.left data.right.left)
          (And.intro data.right.right.left data.right.right.right))

theorem FunctorPrefixHomCarrier_source_prefix_deterministic {p q a target f : BHist} :
    CategoryHomCarrier (append p a) target f →
      CategoryHomCarrier (append q a) target f → hsame p q := by
  intro left right
  have sameSource : hsame (append p a) (append q a) :=
    CategoryHomCarrier_source_deterministic left right
  exact append_right_cancel (k := a) sameSource

theorem FunctorPrefixHomCarrier_comp_source_prefix_deterministic {p q a b c f g fg : BHist} :
    CategoryHomCarrier (append p a) (append p b) f ->
      CategoryHomCarrier (append p b) (append p c) g ->
        Cont f g fg -> CategoryHomCarrier (append q a) (append p c) fg -> hsame p q := by
  intro left right comp displayed
  have composite : CategoryHomCarrier (append p a) (append p c) fg :=
    CategoryHomCarrier_comp_closed left right comp
  have sameSource : hsame (append p a) (append q a) :=
    CategoryHomCarrier_source_deterministic composite displayed
  exact append_right_cancel (k := a) sameSource

theorem FunctorPrefixHomCarrier_source_object_deterministic {p a b target f : BHist} :
    CategoryHomCarrier (append p a) target f →
      CategoryHomCarrier (append p b) target f → hsame a b := by
  intro left right
  have sameSource : hsame (append p a) (append p b) :=
    CategoryHomCarrier_source_deterministic left right
  exact append_left_cancel (h := p) sameSource

theorem FunctorPrefixHomCarrier_target_prefix_deterministic {p q a source f : BHist} :
    CategoryHomCarrier source (append p a) f →
      CategoryHomCarrier source (append q a) f → hsame p q := by
  intro left right
  have sameTarget : hsame (append p a) (append q a) :=
    CategoryHomCarrier_target_deterministic left right
  exact append_right_cancel (k := a) sameTarget

theorem FunctorPrefixHomCarrier_target_object_deterministic {p a b source f : BHist} :
    CategoryHomCarrier source (append p a) f →
      CategoryHomCarrier source (append p b) f → hsame a b := by
  intro left right
  have sameTarget : hsame (append p a) (append p b) :=
    CategoryHomCarrier_target_deterministic left right
  exact append_left_cancel (h := p) sameTarget

theorem FunctorPrefixHomCarrier_comp_middle_object_deterministic
    {p a b b' c f g fg : BHist} :
    CategoryHomCarrier (append p a) (append p b) f →
      CategoryHomCarrier (append p b') (append p c) g → Cont f g fg →
        CategoryHomCarrier (append p a) (append p c) fg → hsame b b' := by
  intro left right comp displayed
  have sameMiddle : hsame (append p b) (append p b') :=
    CategoryHomCarrier_comp_middle_object_deterministic left right comp displayed
  exact append_left_cancel (h := p) sameMiddle

theorem FunctorPrefixHomCarrier_comp_target_prefix_deterministic {p q a b c f g fg : BHist} :
    CategoryHomCarrier (append p a) (append p b) f ->
      CategoryHomCarrier (append p b) (append p c) g -> Cont f g fg ->
        CategoryHomCarrier (append p a) (append q c) fg -> hsame p q := by
  intro left right comp displayed
  have sameTarget : hsame (append p c) (append q c) :=
    CategoryHomCarrier_comp_target_deterministic left right comp displayed
  exact append_right_cancel (k := c) sameTarget

theorem FunctorPrefixHomCarrier_zero_headed_component_absurd {p a b f : BHist} :
    CategoryHomCarrier (append p a) (append p b) f →
      ((∃ z : BHist, p = BHist.e0 z) ∨ (∃ z : BHist, a = BHist.e0 z) ∨
        (∃ z : BHist, b = BHist.e0 z) ∨ (∃ z : BHist, f = BHist.e0 z)) →
        False := by
  intro homCarrier zeroComponent
  cases zeroComponent with
  | inl prefixZero =>
      cases prefixZero with
      | intro z prefixEq =>
          cases prefixEq
          exact unary_no_zero_extension (unary_append_left_factor homCarrier.left)
  | inr rest =>
      cases rest with
      | inl sourceZero =>
          cases sourceZero with
          | intro z sourceEq =>
              cases sourceEq
              exact unary_no_zero_extension (unary_append_right_factor homCarrier.left)
      | inr rest =>
          cases rest with
          | inl targetZero =>
              cases targetZero with
              | intro z targetEq =>
                  cases targetEq
                  exact unary_no_zero_extension
                    (unary_append_right_factor homCarrier.right.left)
          | inr morphZero =>
              cases morphZero with
              | intro z morphEq =>
                  cases morphEq
                  exact unary_no_zero_extension homCarrier.right.right.left

end BEDC.Derived.FunctorUp
