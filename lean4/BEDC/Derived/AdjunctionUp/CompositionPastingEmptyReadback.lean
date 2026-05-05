import BEDC.Derived.AdjunctionUp

namespace BEDC.Derived.AdjunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.NatTransUp

theorem AdjunctionCompositionPasting_empty_readback
    {p21 q21 su sc a tu1 tu2 tc1 tc2 u21 c21 : BHist} :
    NatTransPrefixComponentCarrier p21 su a tu1 ->
      NatTransPrefixComponentCarrier su q21 a tu2 ->
        NatTransPrefixComponentCarrier q21 sc a tc1 ->
          NatTransPrefixComponentCarrier sc p21 a tc2 ->
            Cont tu1 tu2 u21 -> Cont tc1 tc2 c21 -> hsame u21 BHist.Empty ->
              hsame c21 BHist.Empty ->
                (hsame tu1 BHist.Empty ∧ hsame tu2 BHist.Empty ∧ hsame p21 su ∧
                    hsame su q21) ∧
                  (hsame tc1 BHist.Empty ∧ hsame tc2 BHist.Empty ∧ hsame q21 sc ∧
                    hsame sc p21) := by
  intro unitLeft unitRight counitLeft counitRight unitComposite counitComposite
    unitCompositeEmpty counitCompositeEmpty
  have unitReadback :=
    (NatTransPrefixComponentCarrier_vert_comp_result_empty_iff unitLeft unitRight
      unitComposite).mp unitCompositeEmpty
  have counitReadback :=
    (NatTransPrefixComponentCarrier_vert_comp_result_empty_iff counitLeft counitRight
      counitComposite).mp counitCompositeEmpty
  exact And.intro unitReadback counitReadback

end BEDC.Derived.AdjunctionUp
