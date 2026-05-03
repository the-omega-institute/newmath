import BEDC.Derived.FieldUp.RatDenomUnit

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem RatDenomUnitClassifier_empty_context_rat_carrier_iff {p q p' q' h k : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> hsame p' BHist.Empty ->
      hsame q' BHist.Empty ->
        RatDenomUnitClassifier (append p (append h q)) (append p' (append k q')) ->
          (RatHistoryCarrier h <-> RatHistoryCarrier k) := by
  intro sameP sameQ sameP' sameQ' classified
  have core : RatDenomUnitClassifier h k :=
    (RatDenomUnitClassifier_empty_context_iff (p := p) (q := q) (p' := p') (q' := q')
      (h := h) (k := k) sameP sameQ sameP' sameQ').mp classified
  constructor
  · intro ratH
    exact RatHistoryCarrier_hsame_transport core.right.right ratH
  · intro ratK
    exact RatHistoryCarrier_hsame_transport (hsame_symm core.right.right) ratK

end BEDC.Derived.FieldUp
