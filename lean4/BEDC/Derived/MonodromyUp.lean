import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MonodromyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MonodromyTransportCarrier [AskSetup] [PackageSetup]
    (loop base fibre connection returned ledger provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory loop ∧ UnaryHistory base ∧ UnaryHistory fibre ∧ UnaryHistory connection ∧
    UnaryHistory returned ∧ UnaryHistory ledger ∧ UnaryHistory provenance ∧
      UnaryHistory endpoint ∧ Cont loop base ledger ∧ Cont fibre connection returned ∧
        Cont ledger returned provenance ∧ Cont provenance base endpoint ∧
          PkgSig bundle endpoint pkg

theorem MonodromyTransportCarrier_loop_continuation_stability [AskSetup] [PackageSetup]
    {loop base fibre connection returned ledger provenance endpoint loop' base' fibre'
      connection' returned' ledger' provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonodromyTransportCarrier loop base fibre connection returned ledger provenance endpoint
        bundle pkg ->
      hsame loop loop' ->
        hsame base base' ->
          hsame fibre fibre' ->
            hsame connection connection' ->
              Cont loop' base' ledger' ->
                Cont fibre' connection' returned' ->
                  Cont ledger' returned' provenance' ->
                    Cont provenance' base' endpoint' ->
                      PkgSig bundle endpoint' pkg ->
                        MonodromyTransportCarrier loop' base' fibre' connection' returned'
                            ledger' provenance' endpoint' bundle pkg ∧
                          hsame ledger ledger' ∧ hsame returned returned' ∧
                            hsame provenance provenance' ∧ hsame endpoint endpoint' := by
  intro carrier sameLoop sameBase sameFibre sameConnection ledgerCont' returnedCont'
    provenanceCont' endpointCont' pkg'
  have loopUnary' : UnaryHistory loop' :=
    unary_transport carrier.left sameLoop
  have baseUnary' : UnaryHistory base' :=
    unary_transport carrier.right.left sameBase
  have fibreUnary' : UnaryHistory fibre' :=
    unary_transport carrier.right.right.left sameFibre
  have connectionUnary' : UnaryHistory connection' :=
    unary_transport carrier.right.right.right.left sameConnection
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameLoop sameBase
      carrier.right.right.right.right.right.right.right.right.left ledgerCont'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed loopUnary' baseUnary' ledgerCont'
  have sameReturned : hsame returned returned' :=
    cont_respects_hsame sameFibre sameConnection
      carrier.right.right.right.right.right.right.right.right.right.left returnedCont'
  have returnedUnary' : UnaryHistory returned' :=
    unary_cont_closed fibreUnary' connectionUnary' returnedCont'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameLedger sameReturned
      carrier.right.right.right.right.right.right.right.right.right.right.left provenanceCont'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed ledgerUnary' returnedUnary' provenanceCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameBase
      carrier.right.right.right.right.right.right.right.right.right.right.right.left
      endpointCont'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed provenanceUnary' baseUnary' endpointCont'
  exact
    And.intro
      (And.intro loopUnary'
        (And.intro baseUnary'
          (And.intro fibreUnary'
            (And.intro connectionUnary'
              (And.intro returnedUnary'
                (And.intro ledgerUnary'
                  (And.intro provenanceUnary'
                    (And.intro endpointUnary'
                      (And.intro ledgerCont'
                        (And.intro returnedCont'
                          (And.intro provenanceCont'
                            (And.intro endpointCont' pkg'))))))))))))
      (And.intro sameLedger
        (And.intro sameReturned (And.intro sameProvenance sameEndpoint)))

end BEDC.Derived.MonodromyUp
