import BEDC.FKernel.Unary.History

namespace BEDC.FKernel.Unary

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem unary_repetition_closed_under_continuation {h k r : BHist} :
    UnaryHistory h -> UnaryHistory k -> Cont h k r -> UnaryHistory r := by
  intro uh uk hr
  cases hr
  induction k generalizing h with
  | Empty =>
      exact uh
  | e0 k ih =>
      cases uk
  | e1 k ih =>
      exact ih uh uk

end BEDC.FKernel.Unary
