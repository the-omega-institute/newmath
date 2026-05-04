import BEDC.Derived.ComplexSeriesUp

namespace BEDC.Derived.RealAnalyticUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexSeriesUp

theorem RealAnalyticComplexPartSum_index_unary {zero : BHist} {c : BHist -> BHist}
    {n S : BHist} :
    ComplexPartSum zero c n S -> UnaryHistory n := by
  intro sum
  induction sum with
  | zero =>
      exact unary_empty
  | step _ _ ih =>
      exact unary_e1_closed ih

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
      exact unary_cont_closed ih (termUnary (RealAnalyticComplexPartSum_index_unary previous))
        stepContinuation

end BEDC.Derived.RealAnalyticUp
