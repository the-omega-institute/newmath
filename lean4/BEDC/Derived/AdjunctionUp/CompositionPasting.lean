import BEDC.Derived.AdjunctionUp

namespace BEDC.Derived.AdjunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.NatTransUp

theorem AdjunctionCompositionPasting_unit_counit_carrier
    {p21 q21 su sc a tu1 tu2 tc1 tc2 u21 c21 l21 r21 : BHist} :
    NatTransPrefixComponentCarrier p21 su a tu1 ->
      NatTransPrefixComponentCarrier su q21 a tu2 ->
        NatTransPrefixComponentCarrier q21 sc a tc1 ->
          NatTransPrefixComponentCarrier sc p21 a tc2 ->
            Cont tu1 tu2 u21 ->
              Cont tc1 tc2 c21 ->
                Cont u21 c21 l21 ->
                  Cont c21 u21 r21 ->
                    AdjunctionUnitCounitCarrier p21 q21 a u21 c21 l21 r21 := by
  intro unitLeft unitRight counitLeft counitRight unitRel counitRel leftRel rightRel
  have unitCarrier : NatTransPrefixComponentCarrier p21 q21 a u21 :=
    NatTransPrefixComponentCarrier_vert_comp_closed unitLeft unitRight unitRel
  have counitCarrier : NatTransPrefixComponentCarrier q21 p21 a c21 :=
    NatTransPrefixComponentCarrier_vert_comp_closed counitLeft counitRight counitRel
  exact And.intro unitCarrier (And.intro counitCarrier (And.intro leftRel rightRel))

end BEDC.Derived.AdjunctionUp
