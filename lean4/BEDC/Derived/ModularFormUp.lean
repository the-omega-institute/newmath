import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ModularFormUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ModularFormAutomorphicTransport_stability
    {hol hol' auto auto' coeff coeff' transform transform' ledger ledger' endpoint endpoint' :
      BHist} :
    UnaryHistory hol -> UnaryHistory auto -> UnaryHistory coeff -> UnaryHistory transform ->
      hsame hol hol' -> hsame auto auto' -> hsame coeff coeff' ->
        hsame transform transform' -> Cont hol coeff ledger -> Cont hol' coeff' ledger' ->
          Cont auto transform endpoint -> Cont auto' transform' endpoint' ->
            UnaryHistory hol' ∧ UnaryHistory auto' ∧ UnaryHistory coeff' ∧
              UnaryHistory transform' ∧ UnaryHistory ledger' ∧ UnaryHistory endpoint' ∧
                hsame ledger ledger' ∧ hsame endpoint endpoint' := by
  intro holUnary autoUnary coeffUnary transformUnary sameHol sameAuto sameCoeff sameTransform
    ledgerCont ledgerCont' endpointCont endpointCont'
  have holUnary' : UnaryHistory hol' :=
    unary_transport holUnary sameHol
  have autoUnary' : UnaryHistory auto' :=
    unary_transport autoUnary sameAuto
  have coeffUnary' : UnaryHistory coeff' :=
    unary_transport coeffUnary sameCoeff
  have transformUnary' : UnaryHistory transform' :=
    unary_transport transformUnary sameTransform
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed holUnary' coeffUnary' ledgerCont'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed autoUnary' transformUnary' endpointCont'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameHol sameCoeff ledgerCont ledgerCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameAuto sameTransform endpointCont endpointCont'
  exact And.intro holUnary'
    (And.intro autoUnary'
      (And.intro coeffUnary'
        (And.intro transformUnary'
          (And.intro ledgerUnary'
            (And.intro endpointUnary'
              (And.intro sameLedger sameEndpoint))))))

end BEDC.Derived.ModularFormUp
