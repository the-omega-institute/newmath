import BEDC.FKernel.Unary.Commutativity

namespace BEDC.FKernel.Unary

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem unary_commutativity_refined_with_result_closure {h k r r' : BHist} :
    UnaryHistory h -> UnaryHistory k -> Cont h k r -> Cont k h r' ->
      hsame r r' /\ UnaryHistory r /\ UnaryHistory r' := by
  intro uh uk hr hr'
  constructor
  · exact unary_commutativity_refined uh uk hr hr'
  · constructor
    · exact unary_cont_closed uh uk hr
    · exact unary_cont_closed uk uh hr'

end BEDC.FKernel.Unary
