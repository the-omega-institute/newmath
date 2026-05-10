import BEDC.Derived.NatTransUp

namespace BEDC.Derived.NatTransUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def NatTransPrefixComponentFamilyCarrier (p q eta : BHist) : Prop :=
  forall {a : BHist}, UnaryHistory a -> NatTransPrefixComponentCarrier p q a eta

theorem NatTransPrefixComponentFamilyCarrier_vert_comp_closed
    {p q r eta theta composite : BHist} :
    NatTransPrefixComponentFamilyCarrier p q eta ->
      NatTransPrefixComponentFamilyCarrier q r theta ->
        Cont eta theta composite -> NatTransPrefixComponentFamilyCarrier p r composite := by
  intro leftFamily rightFamily comp
  intro a objectUnary
  exact NatTransPrefixComponentCarrier_vert_comp_closed
    (leftFamily objectUnary) (rightFamily objectUnary) comp

theorem NatTransPrefixFunctorCategory_identity_and_composition
    {p q r eta theta composite : BHist} :
    UnaryHistory p -> NatTransPrefixComponentFamilyCarrier p q eta ->
      NatTransPrefixComponentFamilyCarrier q r theta -> Cont eta theta composite ->
        NatTransPrefixComponentFamilyCarrier p p BHist.Empty ∧
          NatTransPrefixComponentFamilyCarrier p r composite := by
  intro pCarrier leftFamily rightFamily comp
  constructor
  · intro a objectUnary
    exact
      (NatTransPrefixComponentCarrier_empty_identity_iff
        (p := p) (q := p) (a := a)).mpr
        (And.intro pCarrier
          (And.intro pCarrier
            (And.intro objectUnary (hsame_refl p))))
  · exact NatTransPrefixComponentFamilyCarrier_vert_comp_closed leftFamily rightFamily comp

theorem NatTransPrefixComponentCarrier_vert_comp_family_public_readback
    {p q r eta theta composite displayed : BHist} :
    (forall {a : BHist}, UnaryHistory a -> NatTransPrefixComponentCarrier p q a eta) ->
      (forall {a : BHist}, UnaryHistory a -> NatTransPrefixComponentCarrier q r a theta) ->
        Cont eta theta composite ->
          (forall {a : BHist}, UnaryHistory a ->
            NatTransPrefixComponentCarrier p r a displayed) ->
            hsame composite displayed := by
  intro leftFamily rightFamily comp displayedFamily
  have leftEmpty :
      NatTransPrefixComponentCarrier p q BHist.Empty eta :=
    leftFamily (a := BHist.Empty) unary_empty
  have rightEmpty :
      NatTransPrefixComponentCarrier q r BHist.Empty theta :=
    rightFamily (a := BHist.Empty) unary_empty
  have displayedEmpty :
      NatTransPrefixComponentCarrier p r BHist.Empty displayed :=
    displayedFamily (a := BHist.Empty) unary_empty
  exact
    (NatTransPrefixComponentCarrier_vert_comp_public_readback leftEmpty rightEmpty comp).right
      displayedEmpty

theorem NatTransPrefixComponentFamilyCarrier_identity_unit_laws {p q eta left right : BHist} :
    NatTransPrefixComponentFamilyCarrier p q eta -> Cont BHist.Empty eta left ->
      Cont eta BHist.Empty right ->
        NatTransPrefixComponentFamilyCarrier p p BHist.Empty ∧
          NatTransPrefixComponentFamilyCarrier p q left ∧
            NatTransPrefixComponentFamilyCarrier p q right ∧ hsame left eta ∧
              hsame right eta ∧ hsame left right := by
  intro familyCarrier leftRel rightRel
  have leftSame : hsame left eta := cont_left_unit_result leftRel
  have rightSame : hsame right eta := cont_deterministic rightRel (cont_right_unit eta)
  have leftFamily : NatTransPrefixComponentFamilyCarrier p q left := by
    intro a objectUnary
    exact
      (NatTransPrefixComponentCarrier_vert_comp_left_identity_closed
        (familyCarrier objectUnary) leftRel).left
  have rightFamily : NatTransPrefixComponentFamilyCarrier p q right := by
    intro a objectUnary
    exact
      (NatTransPrefixComponentCarrier_vert_comp_right_identity_closed
        (familyCarrier objectUnary) rightRel).left
  have identityFamily : NatTransPrefixComponentFamilyCarrier p p BHist.Empty := by
    intro a objectUnary
    have component := familyCarrier objectUnary
    exact
      (NatTransPrefixComponentCarrier_empty_identity_iff (p := p) (q := p) (a := a)).mpr
        (And.intro component.left
          (And.intro component.left
            (And.intro objectUnary (hsame_refl p))))
  exact
    And.intro identityFamily
      (And.intro leftFamily
        (And.intro rightFamily
          (And.intro leftSame
            (And.intro rightSame (hsame_trans leftSame (hsame_symm rightSame))))))

end BEDC.Derived.NatTransUp
