import BEDC.Derived.ComplexSeriesUp

namespace BEDC.Derived.RealAnalyticUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexSeriesUp

theorem RealAnalyticComplexPartSum_result_unary {zero : BHist} {c : BHist -> BHist}
    {n S : BHist}
    (zeroUnary : UnaryHistory zero)
    (termUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (c m)) :
    ComplexPartSum zero c n S -> UnaryHistory S := by
  intro sum
  induction sum with
  | zero =>
      exact zeroUnary
  | step previous stepContinuation ih =>
      have indexUnary :
          forall {m P : BHist}, ComplexPartSum zero c m P -> UnaryHistory m := by
        intro m P previousSum
        induction previousSum with
        | zero =>
            exact unary_empty
        | step _ _ inner =>
            exact unary_e1_closed inner
      exact unary_cont_closed ih (termUnary (indexUnary previous)) stepContinuation

end BEDC.Derived.RealAnalyticUp
