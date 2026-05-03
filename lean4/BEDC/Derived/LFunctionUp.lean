import BEDC.Derived.DirichletSeriesUp

namespace BEDC.Derived.LFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.DirichletSeriesUp

theorem LFunctionDirichletPartSum_successor_positive_index
    {term : BHist -> BHist -> BHist} {s n S : BHist} :
    DirichletPartSum term s n S -> DirichletPositiveIndex (BHist.e1 n) := by
  intro sum
  have unaryN : UnaryHistory n := by
    induction sum with
    | zero =>
        exact unary_empty
    | step _ _ ih =>
        exact unary_e1_closed ih
  exact Exists.intro n (And.intro unaryN rfl)

end BEDC.Derived.LFunctionUp
