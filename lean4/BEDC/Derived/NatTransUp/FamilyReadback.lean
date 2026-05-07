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

end BEDC.Derived.NatTransUp
