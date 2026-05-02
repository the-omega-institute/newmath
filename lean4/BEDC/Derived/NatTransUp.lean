import BEDC.Derived.FunctorUp
import BEDC.Derived.CategoryUp

namespace BEDC.Derived.NatTransUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp
open BEDC.Derived.FunctorUp

theorem NatTransPrefixIdentity_naturality_square {p a b f left right : BHist} :
    UnaryHistory p -> CategoryHomCarrier a b f -> Cont BHist.Empty f left ->
      Cont f BHist.Empty right ->
        CategoryHomCarrier (append p a) (append p b) left ∧
          CategoryHomCarrier (append p a) (append p b) right ∧ hsame left right := by
  intro prefixCarrier homCarrier leftRel rightRel
  have leftSame : hsame left f := cont_left_unit_result leftRel
  have rightSame : hsame right f := cont_deterministic rightRel (cont_right_unit f)
  have leftCarrier : CategoryHomCarrier a b left := by
    cases leftSame
    exact homCarrier
  have rightCarrier : CategoryHomCarrier a b right := by
    cases rightSame
    exact homCarrier
  exact
    And.intro
      (FunctorPrefixHomCarrier_preserves prefixCarrier leftCarrier)
      (And.intro
        (FunctorPrefixHomCarrier_preserves prefixCarrier rightCarrier)
        (leftSame.trans rightSame.symm))

def NatTransPrefixComponentCarrier (p q a eta : BHist) : Prop :=
  UnaryHistory p ∧ UnaryHistory q ∧ UnaryHistory a ∧
    CategoryHomCarrier (append p a) (append q a) eta

theorem NatTransPrefixComponentCarrier_empty_identity_iff {p q a : BHist} :
    NatTransPrefixComponentCarrier p q a BHist.Empty ↔
      UnaryHistory p ∧ UnaryHistory q ∧ UnaryHistory a ∧ hsame p q := by
  constructor
  · intro component
    cases component with
    | intro prefixCarrier rest =>
        cases rest with
        | intro targetPrefixCarrier rest =>
            cases rest with
            | intro objectCarrier homCarrier =>
                have identityData :=
                  Iff.mp CategoryHomCarrier_empty_identity_iff homCarrier
                exact
                  And.intro prefixCarrier
                    (And.intro targetPrefixCarrier
                      (And.intro objectCarrier
                        (append_right_cancel (k := a) identityData.right.right)))
  · intro data
    cases data with
    | intro prefixCarrier rest =>
        cases rest with
        | intro targetPrefixCarrier rest =>
            cases rest with
            | intro objectCarrier samePrefix =>
                have sameComponent :
                    hsame (append p a) (append q a) := by
                  cases samePrefix
                  rfl
                exact
                  And.intro prefixCarrier
                    (And.intro targetPrefixCarrier
                      (And.intro objectCarrier
                        (Iff.mpr CategoryHomCarrier_empty_identity_iff
                          (And.intro
                            (unary_append_closed prefixCarrier objectCarrier)
                            (And.intro
                              (unary_append_closed targetPrefixCarrier objectCarrier)
                              sameComponent)))))

theorem NatTransPrefixComponentCarrier_empty_identity_prefix_trans {p q r a : BHist} :
    NatTransPrefixComponentCarrier p q a BHist.Empty ->
      NatTransPrefixComponentCarrier q r a BHist.Empty -> hsame p r := by
  intro left right
  have leftData := Iff.mp NatTransPrefixComponentCarrier_empty_identity_iff left
  have rightData := Iff.mp NatTransPrefixComponentCarrier_empty_identity_iff right
  exact hsame_trans leftData.right.right.right rightData.right.right.right

theorem NatTransPrefixComponentCarrier_e1_source_empty_component_iff {p q a : BHist} :
    NatTransPrefixComponentCarrier (BHist.e1 p) q a BHist.Empty ↔
      UnaryHistory p ∧ UnaryHistory a ∧ q = BHist.e1 p := by
  constructor
  · intro component
    have identityData :=
      (NatTransPrefixComponentCarrier_empty_identity_iff
        (p := BHist.e1 p) (q := q) (a := a)).mp component
    exact
      And.intro (unary_e1_inversion identityData.left)
        (And.intro identityData.right.right.left
          (hsame_symm identityData.right.right.right))
  · intro data
    cases data with
    | intro prefixCarrier rest =>
        cases rest with
        | intro objectCarrier targetEq =>
            cases targetEq
            exact
              (NatTransPrefixComponentCarrier_empty_identity_iff
                (p := BHist.e1 p) (q := BHist.e1 p) (a := a)).mpr
                (And.intro (unary_e1_closed prefixCarrier)
                  (And.intro (unary_e1_closed prefixCarrier)
                    (And.intro objectCarrier (hsame_refl (BHist.e1 p)))))

theorem NatTransPrefixComponentCarrier_empty_source_prefix_iff {q a eta : BHist} :
    NatTransPrefixComponentCarrier BHist.Empty q a eta ↔
      UnaryHistory q ∧ UnaryHistory a ∧ CategoryHomCarrier a (append q a) eta := by
  constructor
  · intro component
    cases component with
    | intro _emptyCarrier rest =>
        cases rest with
        | intro prefixCarrier rest =>
            cases rest with
            | intro objectCarrier homCarrier =>
                exact
                  And.intro prefixCarrier
                    (And.intro objectCarrier
                      (CategoryHomCarrier_hsame_transport
                        (append_empty_left a) (hsame_refl (append q a)) (hsame_refl eta)
                        homCarrier))
  · intro data
    cases data with
    | intro prefixCarrier rest =>
        cases rest with
        | intro objectCarrier homCarrier =>
            exact
              And.intro unary_empty
                (And.intro prefixCarrier
                  (And.intro objectCarrier
                    (CategoryHomCarrier_hsame_transport
                      (hsame_symm (append_empty_left a)) (hsame_refl (append q a))
                      (hsame_refl eta) homCarrier)))

theorem NatTransPrefixComponentCarrier_empty_target_prefix_iff {p a eta : BHist} :
    NatTransPrefixComponentCarrier p BHist.Empty a eta ↔
      UnaryHistory p ∧ UnaryHistory a ∧ CategoryHomCarrier (append p a) a eta := by
  constructor
  · intro component
    cases component with
    | intro prefixCarrier rest =>
        cases rest with
        | intro _emptyCarrier rest =>
            cases rest with
            | intro objectCarrier homCarrier =>
                exact
                  And.intro prefixCarrier
                    (And.intro objectCarrier
                      (CategoryHomCarrier_hsame_transport
                        (hsame_refl (append p a)) (append_empty_left a) (hsame_refl eta)
                        homCarrier))
  · intro data
    cases data with
    | intro prefixCarrier rest =>
        cases rest with
        | intro objectCarrier homCarrier =>
            exact
              And.intro prefixCarrier
                (And.intro unary_empty
                  (And.intro objectCarrier
                    (CategoryHomCarrier_hsame_transport
                      (hsame_refl (append p a)) (hsame_symm (append_empty_left a))
                      (hsame_refl eta) homCarrier)))

theorem NatTransPrefixComponentCarrier_empty_prefixes_iff {a eta : BHist} :
    NatTransPrefixComponentCarrier BHist.Empty BHist.Empty a eta ↔
      UnaryHistory a ∧ CategoryHomCarrier a a eta := by
  constructor
  · intro component
    cases component with
    | intro _sourcePrefixCarrier rest =>
        cases rest with
        | intro _targetPrefixCarrier rest =>
            cases rest with
            | intro objectCarrier homCarrier =>
                exact
                  And.intro objectCarrier
                    (CategoryHomCarrier_hsame_transport
                      (append_empty_left a) (append_empty_left a) (hsame_refl eta)
                      homCarrier)
  · intro data
    cases data with
    | intro objectCarrier homCarrier =>
        exact
          And.intro unary_empty
            (And.intro unary_empty
              (And.intro objectCarrier
                (CategoryHomCarrier_hsame_transport
                  (hsame_symm (append_empty_left a)) (hsame_symm (append_empty_left a))
                  (hsame_refl eta) homCarrier)))

theorem NatTransPrefixComponentCarrier_vert_comp_closed {p q r a eta theta composite : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q r a theta ->
        Cont eta theta composite -> NatTransPrefixComponentCarrier p r a composite := by
  intro left right comp
  cases left with
  | intro sourceCarrier leftRest =>
      cases leftRest with
      | intro _middleCarrier leftRest =>
          cases leftRest with
          | intro objectCarrier leftComponent =>
              cases right with
              | intro _middleCarrierAgain rightRest =>
                  cases rightRest with
                  | intro targetCarrier rightRest =>
                      cases rightRest with
                      | intro _objectCarrierAgain rightComponent =>
                          exact
                            And.intro sourceCarrier
                              (And.intro targetCarrier
                                (And.intro objectCarrier
                                  (CategoryHomCarrier_comp_closed leftComponent rightComponent comp)))

theorem NatTransPrefixComponentCarrier_vert_comp_public_readback
    {p q r a eta theta composite : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q r a theta ->
        Cont eta theta composite ->
          NatTransPrefixComponentCarrier p r a composite ∧
            (∀ {displayed : BHist},
              NatTransPrefixComponentCarrier p r a displayed -> hsame composite displayed) := by
  intro left right comp
  have compositeCarrier :
      NatTransPrefixComponentCarrier p r a composite :=
    NatTransPrefixComponentCarrier_vert_comp_closed left right comp
  constructor
  · exact compositeCarrier
  · intro displayed displayedCarrier
    exact CategoryHomCarrier_morphism_deterministic compositeCarrier.right.right.right
      displayedCarrier.right.right.right

theorem NatTransPrefixComponentCarrier_vert_comp_right_factor
    {p q r a eta theta composite : BHist} :
    NatTransPrefixComponentCarrier p q a eta -> Cont eta theta composite ->
      NatTransPrefixComponentCarrier p r a composite ->
        NatTransPrefixComponentCarrier q r a theta := by
  intro left comp displayed
  exact
    And.intro left.right.left
      (And.intro displayed.right.left
        (And.intro left.right.right.left
          (CategoryHomCarrier_comp_right_factor left.right.right.right comp
            displayed.right.right.right)))

theorem NatTransPrefixComponentCarrier_vert_comp_right_factor_public_readback
    {p q r a eta theta composite : BHist} :
    NatTransPrefixComponentCarrier p q a eta -> Cont eta theta composite ->
      NatTransPrefixComponentCarrier p r a composite ->
        NatTransPrefixComponentCarrier q r a theta ∧
          (∀ {theta' : BHist}, Cont eta theta' composite ->
            NatTransPrefixComponentCarrier q r a theta' -> hsame theta theta') := by
  intro left comp displayed
  constructor
  · exact NatTransPrefixComponentCarrier_vert_comp_right_factor left comp displayed
  · intro theta' comp' _right
    exact cont_left_cancel comp comp'

theorem NatTransPrefixComponentCarrier_vert_comp_left_factor
    {p q r a eta theta composite : BHist} :
    NatTransPrefixComponentCarrier q r a theta -> Cont eta theta composite ->
      NatTransPrefixComponentCarrier p r a composite ->
        NatTransPrefixComponentCarrier p q a eta := by
  intro right comp displayed
  exact
    And.intro displayed.left
      (And.intro right.left
        (And.intro displayed.right.right.left
          (CategoryHomCarrier_comp_left_factor right.right.right.right comp
            displayed.right.right.right)))

theorem NatTransPrefixComponentCarrier_vert_comp_left_factor_public_readback
    {p q r a eta theta composite : BHist} :
    NatTransPrefixComponentCarrier q r a theta -> Cont eta theta composite ->
      NatTransPrefixComponentCarrier p r a composite ->
        NatTransPrefixComponentCarrier p q a eta /\
          (forall {eta' : BHist}, Cont eta' theta composite ->
            NatTransPrefixComponentCarrier p q a eta' -> hsame eta eta') := by
  intro right comp displayed
  constructor
  · exact NatTransPrefixComponentCarrier_vert_comp_left_factor right comp displayed
  · intro eta' comp' _left
    exact cont_right_cancel comp comp'

theorem NatTransPrefixComponentCarrier_vert_comp_assoc_closed
    {p q r s a eta theta iota etatheta thetaiota left right : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q r a theta ->
        NatTransPrefixComponentCarrier r s a iota ->
          Cont eta theta etatheta -> Cont theta iota thetaiota ->
            Cont etatheta iota left -> Cont eta thetaiota right ->
              NatTransPrefixComponentCarrier p s a left ∧
                NatTransPrefixComponentCarrier p s a right ∧ hsame left right := by
  intro first second third etathetaRel thetaiotaRel leftRel rightRel
  have assocClosed :
      CategoryHomCarrier (append p a) (append s a) left ∧
        CategoryHomCarrier (append p a) (append s a) right ∧ hsame left right :=
    CategoryHomCarrier_comp_assoc_closed first.right.right.right second.right.right.right
      third.right.right.right etathetaRel thetaiotaRel leftRel rightRel
  exact
    And.intro
      (And.intro first.left
        (And.intro third.right.left
          (And.intro first.right.right.left assocClosed.left)))
      (And.intro
        (And.intro first.left
          (And.intro third.right.left
            (And.intro first.right.right.left assocClosed.right.left)))
        assocClosed.right.right)

theorem NatTransPrefixComponentCarrier_tail_comm_hsame
    {p q r a eta theta etatheta thetaeta : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q r a theta ->
        Cont eta theta etatheta -> Cont theta eta thetaeta -> hsame etatheta thetaeta := by
  intro left right etathetaRel thetaetaRel
  exact CategoryHomCarrier_tail_comm_hsame left.2.2.2 right.2.2.2 etathetaRel thetaetaRel

theorem NatTransPrefixIdentity_identity_component_square_closed {p a id left right : BHist} :
    UnaryHistory p -> UnaryHistory a -> Cont BHist.Empty BHist.Empty id ->
      Cont id BHist.Empty left -> Cont BHist.Empty id right ->
        CategoryHomCarrier (append p a) (append p a) left ∧
          CategoryHomCarrier (append p a) (append p a) right ∧ hsame left right := by
  intro prefixCarrier sourceCarrier idRel leftRel rightRel
  have idCarrier : CategoryHomCarrier (append p a) (append p a) id :=
    FunctorPrefixHomCarrier_identity_closed prefixCarrier sourceCarrier idRel
  have leftSame : hsame left id := cont_deterministic leftRel (cont_right_unit id)
  have rightSame : hsame right id := cont_left_unit_result rightRel
  have leftCarrier : CategoryHomCarrier (append p a) (append p a) left := by
    cases leftSame
    exact idCarrier
  have rightCarrier : CategoryHomCarrier (append p a) (append p a) right := by
    cases rightSame
    exact idCarrier
  exact And.intro leftCarrier (And.intro rightCarrier (leftSame.trans rightSame.symm))

theorem NatTransPrefixComponentCarrier_target_prefix_deterministic {p q r a eta : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier p r a eta -> hsame q r := by
  intro left right
  have sameTarget : hsame (append q a) (append r a) :=
    CategoryHomCarrier_target_deterministic left.right.right.right right.right.right.right
  exact append_right_cancel (k := a) sameTarget

theorem NatTransPrefixComponentCarrier_vert_comp_target_prefix_deterministic
    {p q r s a eta theta composite : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q r a theta ->
        Cont eta theta composite ->
          NatTransPrefixComponentCarrier p s a composite -> hsame r s := by
  intro left right comp target
  exact NatTransPrefixComponentCarrier_target_prefix_deterministic
    (NatTransPrefixComponentCarrier_vert_comp_closed left right comp) target

theorem NatTransPrefixComponentCarrier_vert_comp_middle_prefix_deterministic
    {p q q' r a eta theta composite : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q' r a theta ->
        Cont eta theta composite ->
          NatTransPrefixComponentCarrier p r a composite -> hsame q q' := by
  intro left right comp displayed
  have sameMiddle :
      hsame (append q a) (append q' a) :=
    CategoryHomCarrier_comp_middle_object_deterministic left.right.right.right
      right.right.right.right comp displayed.right.right.right
  exact append_right_cancel (k := a) sameMiddle

theorem NatTransPrefixComponentCarrier_source_prefix_deterministic {p q r a eta : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier r q a eta -> hsame p r := by
  intro left right
  have sameSource : hsame (append p a) (append r a) :=
    CategoryHomCarrier_source_deterministic left.right.right.right right.right.right.right
  exact append_right_cancel (k := a) sameSource

theorem NatTransPrefixComponentCarrier_vert_comp_source_prefix_deterministic
    {p q r s a eta theta composite : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q r a theta ->
        Cont eta theta composite ->
          NatTransPrefixComponentCarrier s r a composite -> hsame p s := by
  intro left right comp displayed
  exact NatTransPrefixComponentCarrier_source_prefix_deterministic
    (NatTransPrefixComponentCarrier_vert_comp_closed left right comp) displayed

theorem NatTransPrefixComponentCarrier_vert_comp_right_identity_closed
    {p q a eta right : BHist} :
    NatTransPrefixComponentCarrier p q a eta -> Cont eta BHist.Empty right ->
      NatTransPrefixComponentCarrier p q a right /\ hsame right eta := by
  intro component rightRel
  have rightSame : hsame right eta := cont_deterministic rightRel (cont_right_unit eta)
  have rightCarrier : NatTransPrefixComponentCarrier p q a right := by
    cases rightSame
    exact component
  exact And.intro rightCarrier rightSame

theorem NatTransPrefixComponentCarrier_vert_comp_left_identity_closed
    {p q a eta left : BHist} :
    NatTransPrefixComponentCarrier p q a eta -> Cont BHist.Empty eta left ->
      NatTransPrefixComponentCarrier p q a left /\ hsame left eta := by
  intro component leftRel
  have leftSame : hsame left eta := cont_left_unit_result leftRel
  have leftCarrier : NatTransPrefixComponentCarrier p q a left := by
    cases leftSame
    exact component
  exact And.intro leftCarrier leftSame

theorem NatTransPrefixComponentCarrier_identity_semanticNameCert {p a : BHist} :
    UnaryHistory p -> UnaryHistory a ->
      BEDC.FKernel.NameCert.SemanticNameCert (NatTransPrefixComponentCarrier p p a)
        (NatTransPrefixComponentCarrier p p a) (NatTransPrefixComponentCarrier p p a)
          hsame := by
  intro prefixCarrier objectCarrier
  constructor
  · constructor
    · exact
        Exists.intro BHist.Empty
          (And.intro prefixCarrier
            (And.intro prefixCarrier
              (And.intro objectCarrier
                (CategoryHomCarrier_empty_identity
                  (unary_append_closed prefixCarrier objectCarrier)))))
    · intro h _componentCarrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same componentCarrier
      cases same
      exact componentCarrier
  · intro h source
    exact source
  · intro h source
    exact source

theorem NatTransPrefixComponentCarrier_zero_headed_component_absurd {p q a eta : BHist} :
    NatTransPrefixComponentCarrier p q a eta →
      ((∃ z : BHist, p = BHist.e0 z) ∨ (∃ z : BHist, q = BHist.e0 z) ∨
        (∃ z : BHist, a = BHist.e0 z) ∨ (∃ z : BHist, eta = BHist.e0 z)) →
        False := by
  intro component zeroComponent
  cases zeroComponent with
  | inl sourcePrefixZero =>
      cases sourcePrefixZero with
      | intro z sourcePrefixEq =>
          cases sourcePrefixEq
          exact unary_no_zero_extension component.left
  | inr rest =>
      cases rest with
      | inl targetPrefixZero =>
          cases targetPrefixZero with
          | intro z targetPrefixEq =>
              cases targetPrefixEq
              exact unary_no_zero_extension component.right.left
      | inr rest =>
          cases rest with
          | inl objectZero =>
              cases objectZero with
              | intro z objectEq =>
                  cases objectEq
                  exact unary_no_zero_extension component.right.right.left
          | inr morphZero =>
              cases morphZero with
              | intro z morphEq =>
                  cases morphEq
                  exact unary_no_zero_extension component.right.right.right.right.right.left

end BEDC.Derived.NatTransUp
