import BEDC.Derived.FpsUp

namespace BEDC.Derived.FpsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FpsSingletonAddFold_zero_series_absorption {xs ys : List BHist} :
    FpsSingletonAddFoldSpineCarrier xs ->
      FpsSingletonAddFoldSpineCarrier ys ->
        FpsSingletonClassifier (append (FpsSingletonAddFold xs) (FpsSingletonAddFold ys))
            FpsSingletonZero ∧
          FpsSingletonClassifier (append (FpsSingletonAddFold ys) (FpsSingletonAddFold xs))
            FpsSingletonZero := by
  intro xsSpine ysSpine
  have xsEmpty : hsame (FpsSingletonAddFold xs) BHist.Empty :=
    FpsSingletonAddFold_spine_carrier_empty xsSpine
  have ysEmpty : hsame (FpsSingletonAddFold ys) BHist.Empty :=
    FpsSingletonAddFold_spine_carrier_empty ysSpine
  have leftEmpty :
      hsame (append (FpsSingletonAddFold xs) (FpsSingletonAddFold ys)) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro xsEmpty ysEmpty)
  have rightEmpty :
      hsame (append (FpsSingletonAddFold ys) (FpsSingletonAddFold xs)) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro ysEmpty xsEmpty)
  exact And.intro
    (And.intro leftEmpty (And.intro (hsame_refl BHist.Empty) leftEmpty))
    (And.intro rightEmpty (And.intro (hsame_refl BHist.Empty) rightEmpty))

end BEDC.Derived.FpsUp
