import BEDC.Derived.NatTransUp

namespace BEDC.Derived.NatTransUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

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
