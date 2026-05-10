import BEDC.Derived.NatTransUp.FamilyReadback

namespace BEDC.Derived.NatTransUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem NatTransUp_StdBridge {p q r eta theta composite : BHist} :
    UnaryHistory p →
      NatTransPrefixComponentFamilyCarrier p q eta →
        NatTransPrefixComponentFamilyCarrier q r theta → Cont eta theta composite →
          NatTransPrefixComponentFamilyCarrier p p BHist.Empty ∧
            NatTransPrefixComponentFamilyCarrier p r composite ∧
              (∀ {displayed : BHist},
                NatTransPrefixComponentFamilyCarrier p r displayed → hsame composite displayed) := by
  intro pCarrier leftFamily rightFamily comp
  have inventory :=
    NatTransPrefixFunctorCategory_identity_and_composition pCarrier leftFamily rightFamily comp
  constructor
  · exact inventory.left
  · constructor
    · exact inventory.right
    · intro displayed displayedFamily
      exact
        NatTransPrefixComponentCarrier_vert_comp_family_public_readback
          leftFamily rightFamily comp displayedFamily

end BEDC.Derived.NatTransUp
