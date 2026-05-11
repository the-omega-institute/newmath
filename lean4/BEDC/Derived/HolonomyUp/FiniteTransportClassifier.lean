import BEDC.Derived.HolonomyUp

namespace BEDC.Derived.HolonomyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HolonomyFiniteTransportClassifier [AskSetup] [PackageSetup]
    (loop connection endpoint curvature control ledger provenance loop' connection' endpoint'
      curvature' control' ledger' provenance' : BHist) : Prop :=
  UnaryHistory loop ∧ UnaryHistory connection ∧ UnaryHistory endpoint ∧
    UnaryHistory curvature ∧ UnaryHistory control ∧ UnaryHistory ledger ∧
      UnaryHistory provenance ∧ UnaryHistory loop' ∧ UnaryHistory connection' ∧
        UnaryHistory endpoint' ∧ UnaryHistory curvature' ∧ UnaryHistory control' ∧
          UnaryHistory ledger' ∧ UnaryHistory provenance' ∧ hsame loop loop' ∧
            hsame connection connection' ∧ hsame endpoint endpoint' ∧
              hsame curvature curvature' ∧ hsame control control' ∧ hsame ledger ledger' ∧
                hsame provenance provenance' ∧ Cont loop connection ledger ∧
                  Cont loop' connection' ledger'

end BEDC.Derived.HolonomyUp
