import BEDC.Derived.AdjunctionUp
import BEDC.Derived.NatTransUp.PrefixComponentClassifier

namespace BEDC.Derived.AdjunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.NatTransUp

theorem AdjunctionRightAdjoint_natural_isomorphism_uniqueness
    {p q1 q2 a u1 c1 l1 r1 u2 c2 l2 r2 eta eta' I1 I2 : BHist} :
    AdjunctionUnitCounitCarrier p q1 a u1 c1 l1 r1 ->
      AdjunctionUnitCounitCarrier p q2 a u2 c2 l2 r2 ->
        Cont c1 u2 eta -> Cont c2 u1 eta' -> Cont eta eta' I1 -> Cont eta' eta I2 ->
          NatTransPrefixComponentCarrier q1 q2 a eta ∧
            NatTransPrefixComponentCarrier q2 q1 a eta' ∧
              NatTransPrefixComponentClassifier q1 q1 a I1 BHist.Empty ∧
                NatTransPrefixComponentClassifier q2 q2 a I2 BHist.Empty := by
  intro first second c1u2 c2u1 etaEta' eta'Eta
  have etaCarrier : NatTransPrefixComponentCarrier q1 q2 a eta :=
    NatTransPrefixComponentCarrier_vert_comp_closed first.right.left second.left c1u2
  have eta'Carrier : NatTransPrefixComponentCarrier q2 q1 a eta' :=
    NatTransPrefixComponentCarrier_vert_comp_closed second.right.left first.left c2u1
  have I1Carrier : NatTransPrefixComponentCarrier q1 q1 a I1 :=
    NatTransPrefixComponentCarrier_vert_comp_closed etaCarrier eta'Carrier etaEta'
  have I2Carrier : NatTransPrefixComponentCarrier q2 q2 a I2 :=
    NatTransPrefixComponentCarrier_vert_comp_closed eta'Carrier etaCarrier eta'Eta
  have I1Data :=
    Iff.mp NatTransPrefixComponentCarrier_endomorphism_component_empty_iff I1Carrier
  have I2Data :=
    Iff.mp NatTransPrefixComponentCarrier_endomorphism_component_empty_iff I2Carrier
  have I1Empty : hsame I1 BHist.Empty :=
    I1Data.right.right.right
  have I2Empty : hsame I2 BHist.Empty :=
    I2Data.right.right.right
  have I1EmptyCarrier : NatTransPrefixComponentCarrier q1 q1 a BHist.Empty := by
    cases I1Empty
    exact I1Carrier
  have I2EmptyCarrier : NatTransPrefixComponentCarrier q2 q2 a BHist.Empty := by
    cases I2Empty
    exact I2Carrier
  have I1Classified :
      NatTransPrefixComponentClassifier q1 q1 a I1 BHist.Empty :=
    And.intro I1Carrier.left
      (And.intro I1Carrier.right.left
        (And.intro I1Carrier.right.right.left
          (And.intro I1Carrier.right.right.right
            (And.intro I1EmptyCarrier.right.right.right I1Empty))))
  have I2Classified :
      NatTransPrefixComponentClassifier q2 q2 a I2 BHist.Empty :=
    And.intro I2Carrier.left
      (And.intro I2Carrier.right.left
        (And.intro I2Carrier.right.right.left
          (And.intro I2Carrier.right.right.right
            (And.intro I2EmptyCarrier.right.right.right I2Empty))))
  exact And.intro etaCarrier
    (And.intro eta'Carrier (And.intro I1Classified I2Classified))

end BEDC.Derived.AdjunctionUp
