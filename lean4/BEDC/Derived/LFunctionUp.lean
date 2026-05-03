import BEDC.Derived.DirichletSeriesUp

namespace BEDC.Derived.LFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
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

theorem LFunctionDirichletPartSum_successor_previous_unique
    {term : BHist -> BHist -> BHist} {s n S : BHist} :
    DirichletPartSum term s (BHist.e1 n) S ->
      exists P : BHist, DirichletPartSum term s n P ∧ Cont P (term n s) S ∧
        (forall T : BHist, DirichletPartSum term s n T -> hsame P T) := by
  intro sum
  cases sum with
  | step previous stepContinuation =>
      have unaryN : UnaryHistory n := by
        have positiveIndex : DirichletPositiveIndex (BHist.e1 n) :=
          LFunctionDirichletPartSum_successor_positive_index previous
        cases positiveIndex with
        | intro tail data =>
            cases data with
            | intro unaryTail sameSuccessor =>
                cases sameSuccessor
                exact unaryTail
      exact Exists.intro _
        (And.intro previous
          (And.intro stepContinuation
            (fun T other =>
              DirichletPartSum_unary_index_deterministic unaryN previous other)))

theorem LFunctionDirichletPartSum_zero_term_successor_stable
    {term : BHist -> BHist -> BHist} {s n S : BHist} :
    DirichletPartSum term s n S -> hsame (term n s) BHist.Empty ->
      DirichletPartSum term s (BHist.e1 n) S := by
  intro sum termEmpty
  have stepContinuation : Cont S (term n s) S := by
    exact cont_intro (((congrArg (append S) termEmpty).trans (append_empty_right S)).symm)
  exact DirichletPartSum.step sum stepContinuation

end BEDC.Derived.LFunctionUp
