import BEDC.Derived.AdjunctionUp

namespace BEDC.Derived.AdjunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.NatTransUp

def AdjunctionCompositionPastingData
    (p1 q1 a1 u1 c1 l1 r1 p2 q2 a2 u2 c2 l2 r2 p21 q21 su sc a tu1 tu2 tc1 tc2
      u21 c21 l21 r21 : BHist) : Prop :=
  AdjunctionUnitCounitCarrier p1 q1 a1 u1 c1 l1 r1 ∧
    AdjunctionUnitCounitCarrier p2 q2 a2 u2 c2 l2 r2 ∧
      NatTransPrefixComponentCarrier p21 su a tu1 ∧
        NatTransPrefixComponentCarrier su q21 a tu2 ∧
          NatTransPrefixComponentCarrier q21 sc a tc1 ∧
            NatTransPrefixComponentCarrier sc p21 a tc2 ∧
              Cont tu1 tu2 u21 ∧ Cont tc1 tc2 c21 ∧
                Cont u21 c21 l21 ∧ Cont c21 u21 r21

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

theorem AdjunctionUnitCounitCarrier_composition_pasting_closed
    {p1 q1 a1 u1 c1 l1 r1 p2 q2 a2 u2 c2 l2 r2 p21 q21 su sc a tu1 tu2 tc1 tc2 u21 c21 l21 r21 : BHist} :
    AdjunctionUnitCounitCarrier p1 q1 a1 u1 c1 l1 r1 ->
      AdjunctionUnitCounitCarrier p2 q2 a2 u2 c2 l2 r2 ->
        NatTransPrefixComponentCarrier p21 su a tu1 ->
          NatTransPrefixComponentCarrier su q21 a tu2 ->
            NatTransPrefixComponentCarrier q21 sc a tc1 ->
              NatTransPrefixComponentCarrier sc p21 a tc2 ->
                Cont tu1 tu2 u21 ->
                  Cont tc1 tc2 c21 ->
                    Cont u21 c21 l21 ->
                      Cont c21 u21 r21 ->
                        AdjunctionUnitCounitCarrier p21 q21 a u21 c21 l21 r21 := by
  intro _leftCarrier _rightCarrier unitLeft unitRight counitLeft counitRight unitComp
    counitComp leftTriangle rightTriangle
  exact
    And.intro
      (NatTransPrefixComponentCarrier_vert_comp_closed unitLeft unitRight unitComp)
      (And.intro
        (NatTransPrefixComponentCarrier_vert_comp_closed counitLeft counitRight counitComp)
        (And.intro leftTriangle rightTriangle))

theorem AdjunctionCompositionPasting_triangle_determinacy
    {p21 q21 su sc a tu1 tu2 tc1 tc2 u21 c21 l21 r21 l21' r21' : BHist} :
    NatTransPrefixComponentCarrier p21 su a tu1 ->
      NatTransPrefixComponentCarrier su q21 a tu2 ->
        NatTransPrefixComponentCarrier q21 sc a tc1 ->
          NatTransPrefixComponentCarrier sc p21 a tc2 ->
            Cont tu1 tu2 u21 ->
              Cont tc1 tc2 c21 ->
                Cont u21 c21 l21 ->
                  Cont c21 u21 r21 ->
                    Cont u21 c21 l21' ->
                      Cont c21 u21 r21' ->
                        hsame l21 l21' ∧ hsame r21 r21' := by
  intro _unitLeft _unitRight _counitLeft _counitRight _unitRel _counitRel leftTriangle
    rightTriangle displayedLeft displayedRight
  exact
    And.intro
      (cont_deterministic leftTriangle displayedLeft)
      (cont_deterministic rightTriangle displayedRight)

theorem AdjunctionCompositionPasting_triangle_results_deterministic
    {p21 q21 su sc a tu1 tu2 tc1 tc2 u21 c21 l21 r21 l21' r21' : BHist} :
    NatTransPrefixComponentCarrier p21 su a tu1 ->
      NatTransPrefixComponentCarrier su q21 a tu2 ->
        NatTransPrefixComponentCarrier q21 sc a tc1 ->
          NatTransPrefixComponentCarrier sc p21 a tc2 ->
            Cont tu1 tu2 u21 ->
              Cont tc1 tc2 c21 ->
                Cont u21 c21 l21 ->
                  Cont c21 u21 r21 ->
                    Cont u21 c21 l21' ->
                      Cont c21 u21 r21' -> hsame l21 l21' ∧ hsame r21 r21' := by
  intro unitLeft unitRight counitLeft counitRight unitComp counitComp leftTriangle
    rightTriangle leftTriangle' rightTriangle'
  have carrier : AdjunctionUnitCounitCarrier p21 q21 a u21 c21 l21 r21 :=
    AdjunctionCompositionPasting_unit_counit_carrier unitLeft unitRight counitLeft
      counitRight unitComp counitComp leftTriangle rightTriangle
  exact AdjunctionUnitCounitCarrier_triangle_results_deterministic carrier leftTriangle'
    rightTriangle'

end BEDC.Derived.AdjunctionUp
