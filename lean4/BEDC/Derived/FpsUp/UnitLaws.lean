import BEDC.Derived.FpsUp

namespace BEDC.Derived.FpsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def FpsSingletonUnitSeriesCoeff : BHist -> BHist
  | BHist.Empty => FpsSingletonOne
  | BHist.e0 _ => FpsSingletonZero
  | BHist.e1 _ => FpsSingletonZero

theorem FpsSingletonCauchyProduct_unit_laws {F : BHist} :
    FpsSingletonCarrier F ->
      FpsSingletonCarrier FpsSingletonOne ∧
        FpsSingletonCarrier (FpsSingletonMul FpsSingletonOne F) ∧
          FpsSingletonCarrier (FpsSingletonMul F FpsSingletonOne) ∧
            Cont FpsSingletonOne F (FpsSingletonMul FpsSingletonOne F) ∧
              Cont F FpsSingletonOne (FpsSingletonMul F FpsSingletonOne) ∧
                FpsSingletonClassifier (FpsSingletonMul FpsSingletonOne F) F ∧
                  FpsSingletonClassifier (FpsSingletonMul F FpsSingletonOne) F := by
  intro carrierF
  cases carrierF
  have emptyCarrier : FpsSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassifier : FpsSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  exact And.intro emptyCarrier
    (And.intro emptyCarrier
      (And.intro emptyCarrier
        (And.intro rfl
          (And.intro rfl
            (And.intro emptyClassifier emptyClassifier)))))

end BEDC.Derived.FpsUp
