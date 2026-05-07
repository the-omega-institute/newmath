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

theorem PdeCarriedSourceRow_carrier_obligation_surface
    {manifold derivative relation boundary relationBoundary endpoint : BHist} :
    UnaryHistory manifold -> UnaryHistory derivative -> UnaryHistory relation ->
      UnaryHistory boundary -> Cont relation boundary relationBoundary ->
        Cont (append manifold derivative) relationBoundary endpoint ->
          UnaryHistory manifold ∧ UnaryHistory derivative ∧ UnaryHistory relation ∧
            UnaryHistory boundary ∧ UnaryHistory relationBoundary ∧ UnaryHistory endpoint ∧
              Cont relation boundary relationBoundary ∧
                Cont (append manifold derivative) relationBoundary endpoint := by
  intro manifoldUnary derivativeUnary relationUnary boundaryUnary relationBoundaryCont endpointCont
  have relationBoundaryUnary : UnaryHistory relationBoundary :=
    unary_cont_closed relationUnary boundaryUnary relationBoundaryCont
  have manifoldDerivativeUnary : UnaryHistory (append manifold derivative) :=
    unary_append_closed manifoldUnary derivativeUnary
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed manifoldDerivativeUnary relationBoundaryUnary endpointCont
  exact And.intro manifoldUnary
    (And.intro derivativeUnary
      (And.intro relationUnary
        (And.intro boundaryUnary
          (And.intro relationBoundaryUnary
            (And.intro endpointUnary
              (And.intro relationBoundaryCont endpointCont))))))

theorem PdeCarriedSourceRow_stability_ledger_exactness_obligation_surface
    {manifold derivative relation boundary relationBoundary endpoint
      manifold' derivative' relation' boundary' relationBoundary' endpoint' : BHist} :
    UnaryHistory manifold' -> UnaryHistory derivative' -> UnaryHistory relation' ->
      UnaryHistory boundary' -> hsame manifold manifold' -> hsame derivative derivative' ->
        hsame relation relation' -> hsame boundary boundary' ->
          Cont relation boundary relationBoundary ->
            Cont relation' boundary' relationBoundary' ->
              Cont (append manifold derivative) relationBoundary endpoint ->
                Cont (append manifold' derivative') relationBoundary' endpoint' ->
                  UnaryHistory relationBoundary' ∧ UnaryHistory endpoint' ∧
                    hsame relationBoundary relationBoundary' ∧ hsame endpoint endpoint' ∧
                      Cont relation' boundary' relationBoundary' ∧
                        Cont (append manifold' derivative') relationBoundary' endpoint' := by
  intro manifoldUnary derivativeUnary relationUnary boundaryUnary
  intro manifoldSame derivativeSame relationSame boundarySame
  intro relationBoundaryCont relationBoundaryCont' endpointCont endpointCont'
  have relationBoundaryUnary : UnaryHistory relationBoundary' :=
    unary_cont_closed relationUnary boundaryUnary relationBoundaryCont'
  have sourceSame : hsame (append manifold derivative) (append manifold' derivative') := by
    cases manifoldSame
    cases derivativeSame
    rfl
  have relationBoundarySame : hsame relationBoundary relationBoundary' :=
    cont_respects_hsame relationSame boundarySame relationBoundaryCont relationBoundaryCont'
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame sourceSame relationBoundarySame endpointCont endpointCont'
  have endpointUnary : UnaryHistory endpoint' :=
    unary_cont_closed
      (unary_append_closed manifoldUnary derivativeUnary)
      relationBoundaryUnary
      endpointCont'
  exact And.intro relationBoundaryUnary
    (And.intro endpointUnary
      (And.intro relationBoundarySame
        (And.intro endpointSame (And.intro relationBoundaryCont' endpointCont'))))

end BEDC.Derived.PdeUp
