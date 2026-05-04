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

theorem RealAnalyticComplexPartSum_pointwise_result_unary_transport {zero zero' : BHist}
    {c d : BHist -> BHist} {n S T : BHist}
    (zeroUnary : UnaryHistory zero)
    (sameZero : hsame zero zero')
    (termUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (c m))
    (termSame : forall {m : BHist}, UnaryHistory m -> hsame (c m) (d m)) :
    UnaryHistory n -> ComplexPartSum zero c n S -> ComplexPartSum zero' d n T ->
      UnaryHistory T := by
  intro unaryN source target
  have sourceUnary : UnaryHistory S :=
    RealAnalyticComplexPartSum_result_unary zeroUnary termUnary source
  have sameResult : hsame S T :=
    ComplexPartSum_pointwise_hsame_deterministic sameZero termSame unaryN source target
  exact unary_transport sourceUnary sameResult

theorem RealAnalyticComplexAbsPartSum_pointwise_result_unary_transport {zero zero' : BHist}
    {modulus modulus' : BHist -> BHist} {n M T : BHist}
    (zeroUnary : UnaryHistory zero)
    (sameZero : hsame zero zero')
    (modulusUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (modulus m))
    (modulusSame : forall {m : BHist}, UnaryHistory m -> hsame (modulus m) (modulus' m)) :
    UnaryHistory n -> ComplexAbsPartSum zero modulus n M ->
      ComplexAbsPartSum zero' modulus' n T -> UnaryHistory T := by
  intro unaryN source target
  have sourceUnary : UnaryHistory M :=
    ComplexAbsPartSum_result_unary zeroUnary modulusUnary source
  have sameResult : hsame M T :=
    ComplexAbsPartSum_pointwise_hsame_deterministic sameZero modulusSame unaryN source target
  exact unary_transport sourceUnary sameResult

end BEDC.Derived.RealAnalyticUp
