import BEDC.FKernel.Unary

namespace BEDC.Derived.PdeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem PdeCarriedSourceRow_ledger_exactness_surface
    {manifold derivative relation boundary relationBoundary endpoint : BHist} :
    UnaryHistory manifold -> UnaryHistory derivative -> UnaryHistory relation ->
      UnaryHistory boundary -> Cont relation boundary relationBoundary ->
        Cont (append manifold derivative) relationBoundary endpoint ->
          UnaryHistory relationBoundary ∧ UnaryHistory endpoint ∧
            Cont relation boundary relationBoundary ∧
              Cont (append manifold derivative) relationBoundary endpoint := by
  intro manifoldUnary derivativeUnary relationUnary boundaryUnary relationBoundaryCont endpointCont
  have relationBoundaryUnary : UnaryHistory relationBoundary :=
    unary_cont_closed relationUnary boundaryUnary relationBoundaryCont
  have manifoldDerivativeUnary : UnaryHistory (append manifold derivative) :=
    unary_append_closed manifoldUnary derivativeUnary
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed manifoldDerivativeUnary relationBoundaryUnary endpointCont
  exact And.intro relationBoundaryUnary
    (And.intro endpointUnary (And.intro relationBoundaryCont endpointCont))

end BEDC.Derived.PdeUp
