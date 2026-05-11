import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ControlObservabilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ControlObservabilityFiniteObservationPacket [AskSetup] [PackageSetup]
    (state transition output observationRows observationMatrix traceLedger provenance
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧ UnaryHistory transition ∧ UnaryHistory output ∧
    Cont output transition observationRows ∧ Cont observationRows state observationMatrix ∧
      Cont observationMatrix provenance traceLedger ∧
        Cont traceLedger provenance endpoint ∧ PkgSig bundle endpoint pkg

theorem ControlObservabilityFiniteObservationPacket_classifier_transport [AskSetup]
    [PackageSetup]
    {state state' transition transition' output output' observationRows observationRows'
      observationMatrix observationMatrix' traceLedger traceLedger' provenance provenance'
      endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ControlObservabilityFiniteObservationPacket state transition output observationRows
        observationMatrix traceLedger provenance endpoint bundle pkg ->
      hsame state state' ->
        hsame transition transition' ->
          hsame output output' ->
            hsame provenance provenance' ->
              Cont output' transition' observationRows' ->
                Cont observationRows' state' observationMatrix' ->
                  Cont observationMatrix' provenance' traceLedger' ->
                    Cont traceLedger' provenance' endpoint' ->
                      PkgSig bundle endpoint' pkg ->
                        ControlObservabilityFiniteObservationPacket state' transition' output'
                            observationRows' observationMatrix' traceLedger' provenance'
                            endpoint' bundle pkg ∧
                          hsame observationRows observationRows' ∧
                            hsame observationMatrix observationMatrix' ∧
                              hsame traceLedger traceLedger' ∧ hsame endpoint endpoint' := by
  intro packet sameState sameTransition sameOutput sameProvenance observationRowsRow
    observationMatrixRow traceLedgerRow endpointRow endpointPkg
  have stateUnary : UnaryHistory state' :=
    unary_transport packet.left sameState
  have transitionUnary : UnaryHistory transition' :=
    unary_transport packet.right.left sameTransition
  have outputUnary : UnaryHistory output' :=
    unary_transport packet.right.right.left sameOutput
  have sameObservationRows : hsame observationRows observationRows' :=
    cont_respects_hsame sameOutput sameTransition packet.right.right.right.left
      observationRowsRow
  have sameObservationMatrix : hsame observationMatrix observationMatrix' :=
    cont_respects_hsame sameObservationRows sameState packet.right.right.right.right.left
      observationMatrixRow
  have sameTraceLedger : hsame traceLedger traceLedger' :=
    cont_respects_hsame sameObservationMatrix sameProvenance
      packet.right.right.right.right.right.left traceLedgerRow
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameTraceLedger sameProvenance
      packet.right.right.right.right.right.right.left endpointRow
  exact And.intro
    (And.intro stateUnary
      (And.intro transitionUnary
        (And.intro outputUnary
          (And.intro observationRowsRow
            (And.intro observationMatrixRow
              (And.intro traceLedgerRow
                (And.intro endpointRow endpointPkg)))))))
    (And.intro sameObservationRows
      (And.intro sameObservationMatrix
        (And.intro sameTraceLedger sameEndpoint)))

end BEDC.Derived.ControlObservabilityUp
