import BEDC.Derived.FpsUp.CauchyProductAssociativity
import BEDC.Derived.FpsUp.UnitLaws

namespace BEDC.Derived.FpsUp

open BEDC.FKernel.Hist

theorem FpsSingletonCauchyProduct_multiplicative_monoid_laws :
    hsame FpsSingletonOne BHist.Empty ∧
      FpsSingletonCarrier FpsSingletonOne ∧
        (forall {F G : BHist}, FpsSingletonCarrier F -> FpsSingletonCarrier G ->
          FpsSingletonCarrier (FpsSingletonMul F G)) ∧
        (forall {F G F' G' : BHist}, FpsSingletonClassifier F F' ->
          FpsSingletonClassifier G G' ->
            FpsSingletonClassifier (FpsSingletonMul F G) (FpsSingletonMul F' G')) ∧
        (forall {F G H : BHist},
          FpsSingletonClassifier (FpsSingletonMul (FpsSingletonMul F G) H)
            (FpsSingletonMul F (FpsSingletonMul G H))) ∧
        (forall {F : BHist}, FpsSingletonCarrier F ->
          FpsSingletonClassifier (FpsSingletonMul FpsSingletonOne F) F ∧
            FpsSingletonClassifier (FpsSingletonMul F FpsSingletonOne) F) := by
  have emptyCarrier : FpsSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassifier : FpsSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  constructor
  · exact hsame_refl BHist.Empty
  · constructor
    · exact emptyCarrier
    · constructor
      · intro _F _G _carrierF _carrierG
        exact emptyCarrier
      · constructor
        · intro _F _G _F' _G' _sameF _sameG
          exact emptyClassifier
        · constructor
          · intro F G H
            exact (FpsSingletonCauchyProduct_assoc_classifier (F := F) (G := G) (H := H)).left
          · intro F carrierF
            have laws := FpsSingletonCauchyProduct_unit_laws (F := F) carrierF
            exact And.intro laws.right.right.right.right.right.left
              laws.right.right.right.right.right.right

end BEDC.Derived.FpsUp
