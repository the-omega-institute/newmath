import BEDC.Derived.ComplexSeriesUp

namespace BEDC.Derived.DirichletSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

inductive DirichletPartSum (term : BHist -> BHist -> BHist) (s : BHist) :
    BHist -> BHist -> Prop where
  | zero : DirichletPartSum term s BHist.Empty BHist.Empty
  | step {n S T : BHist} :
      DirichletPartSum term s n S -> Cont S (term n s) T ->
        DirichletPartSum term s (BHist.e1 n) T

theorem DirichletPartSum_successor_result_deterministic
    {term : BHist -> BHist -> BHist} {s n S T U : BHist} :
    DirichletPartSum term s n S -> Cont S (term n s) T ->
      DirichletPartSum term s (BHist.e1 n) U -> hsame T U := by
  have deterministic :
      forall {n S T : BHist},
        DirichletPartSum term s n S -> DirichletPartSum term s n T -> hsame S T := by
    intro n S T left
    induction left generalizing T with
    | zero =>
        intro right
        cases right with
        | zero =>
            exact hsame_refl BHist.Empty
    | step leftSum leftStep ih =>
        intro right
        cases right with
        | step rightSum rightStep =>
            have samePartial := ih rightSum
            exact cont_respects_hsame samePartial (hsame_refl (term _ s)) leftStep rightStep
  intro previous step final
  cases final with
  | step finalPrevious finalStep =>
      have samePrevious := deterministic previous finalPrevious
      exact cont_respects_hsame samePrevious (hsame_refl (term n s)) step finalStep

end BEDC.Derived.DirichletSeriesUp
