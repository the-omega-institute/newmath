import BEDC.Derived.WeylGroupUp

namespace BEDC.Derived.WeylGroupUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem WeylGroupActionTrace_public_boundary {support : ProbeBundle BHist}
    {Vector Nonzero : BHist -> Prop}
    (vector_unary : forall {h : BHist}, Vector h -> UnaryHistory h)
    {root endpoint audit : BHist} {words : List BHist} :
    WeylGroupActionTrace support Vector Nonzero root words endpoint ->
      Cont endpoint BHist.Empty audit ->
        hsame audit root ∧ UnaryHistory audit ∧ hsame endpoint root := by
  intro trace auditStep
  have traceRows := WeylGroupActionTrace_classifier_stability_row vector_unary trace
  have auditSameEndpoint : hsame audit endpoint := cont_right_unit_result auditStep
  exact And.intro (hsame_trans auditSameEndpoint traceRows.left)
    (And.intro (unary_transport traceRows.right (hsame_symm auditSameEndpoint)) traceRows.left)

end BEDC.Derived.WeylGroupUp
