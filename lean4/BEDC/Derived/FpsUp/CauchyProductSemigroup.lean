import BEDC.Derived.FpsUp

namespace BEDC.Derived.FpsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FpsSingletonCauchyProduct_multiplicative_semigroup_laws {F G H F' G' : BHist} :
    FpsSingletonCarrier F -> FpsSingletonCarrier G -> FpsSingletonCarrier H ->
      FpsSingletonClassifier F F' -> FpsSingletonClassifier G G' ->
        FpsSingletonCarrier (FpsSingletonMul F G) ∧
          FpsSingletonClassifier (FpsSingletonMul F G) (FpsSingletonMul F' G') ∧
            FpsSingletonClassifier (FpsSingletonMul (FpsSingletonMul F G) H)
              (FpsSingletonMul F (FpsSingletonMul G H)) ∧
              hsame (append (FpsSingletonMul F G) H) BHist.Empty := by
  intro carrierF carrierG carrierH classifiedF classifiedG
  have carrierF' : FpsSingletonCarrier F' := classifiedF.right.left
  have carrierG' : FpsSingletonCarrier G' := classifiedG.right.left
  have mulCarrier : FpsSingletonCarrier (FpsSingletonMul F G) := hsame_refl BHist.Empty
  have mulPrimeCarrier : FpsSingletonCarrier (FpsSingletonMul F' G') :=
    hsame_refl BHist.Empty
  have assocLeftCarrier : FpsSingletonCarrier (FpsSingletonMul (FpsSingletonMul F G) H) :=
    hsame_refl BHist.Empty
  have assocRightCarrier : FpsSingletonCarrier (FpsSingletonMul F (FpsSingletonMul G H)) :=
    hsame_refl BHist.Empty
  have endpoint :
      hsame (append (FpsSingletonMul F G) H) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro mulCarrier carrierH)
  exact And.intro mulCarrier
    (And.intro
      (And.intro mulCarrier (And.intro mulPrimeCarrier (hsame_refl BHist.Empty)))
      (And.intro
        (And.intro assocLeftCarrier
          (And.intro assocRightCarrier (hsame_refl BHist.Empty)))
        endpoint))

end BEDC.Derived.FpsUp
