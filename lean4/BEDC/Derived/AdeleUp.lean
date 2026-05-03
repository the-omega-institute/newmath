import BEDC.Derived.RealUp
import BEDC.Derived.PadicUp

namespace BEDC.Derived.AdeleUp

open BEDC.FKernel.Hist
open BEDC.Derived.RatUp
open BEDC.Derived.PadicUp

theorem AdeleConstantSliceCarrier_hsame_transport {h h' : BHist} :
    (let AdeleConstantSliceCarrier : BHist -> Prop := fun x =>
      ∃ d : BHist, ∃ p : BHist, ∃ exponent : BHist, ∃ result : BHist,
        hsame x (BHist.e1 d) ∧ RatHistoryCarrier d ∧
          PadicPrimeScale p exponent result;
      hsame h h' -> AdeleConstantSliceCarrier h -> AdeleConstantSliceCarrier h') := by
  exact fun sameHH' carrier =>
    match carrier with
    | ⟨d, p, exponent, result, sameH, ratCarrier, scale⟩ =>
        ⟨d, p, exponent, result, hsame_trans (hsame_symm sameHH') sameH, ratCarrier, scale⟩

end BEDC.Derived.AdeleUp
