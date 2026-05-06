import BEDC.Derived.FpsUp

namespace BEDC.Derived.FpsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FpsSingletonPointwiseAdditionCoeff_empty_ledger {F G n : BHist} :
    hsame (FpsSingletonPointwiseAdditionCoeff F G n) BHist.Empty ∧
      FpsSingletonClassifier (FpsSingletonPointwiseAdditionCoeff F G n) BHist.Empty := by
  have coeffEmpty :
      hsame (FpsSingletonPointwiseAdditionCoeff F G n) BHist.Empty :=
    append_eq_empty_iff.mpr
      (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
  exact And.intro coeffEmpty
    (And.intro coeffEmpty
      (And.intro (hsame_refl BHist.Empty) coeffEmpty))

end BEDC.Derived.FpsUp
