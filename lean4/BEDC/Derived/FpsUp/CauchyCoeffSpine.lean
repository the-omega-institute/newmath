import BEDC.Derived.FpsUp

namespace BEDC.Derived.FpsUp

open BEDC.FKernel.Hist

def FpsSingletonCauchyCoeffSpine (F G n : BHist) : List BHist :=
  [FpsSingletonMul (FpsSingletonCoeff F n) (FpsSingletonCoeff G BHist.Empty)]

theorem FpsSingletonCauchyCoeffSpine_carrier {F G n : BHist} :
    FpsSingletonAddFoldSpineCarrier (FpsSingletonCauchyCoeffSpine F G n) ∧
      FpsSingletonClassifier (FpsSingletonAddFold (FpsSingletonCauchyCoeffSpine F G n))
        (FpsSingletonMul (FpsSingletonCoeff F n) (FpsSingletonCoeff G BHist.Empty)) := by
  have emptyCarrier : FpsSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  exact And.intro (And.intro emptyCarrier (hsame_refl BHist.Empty))
    (And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty)))

end BEDC.Derived.FpsUp
