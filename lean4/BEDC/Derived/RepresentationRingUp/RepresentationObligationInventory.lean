import BEDC.Derived.RepresentationRingUp.InducedConsumerBoundary
import BEDC.Derived.RepresentationRingUp.OperationLedgerCoverage

namespace BEDC.Derived.RepresentationRingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RepresentationRingBHistRepresentationPacket_obligation_inventory_sound [AskSetup]
    [PackageSetup]
    {group ring reps directSum tensor provenance classifier ledger endpoint directSumEndpoint
      tensorEndpoint inducedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RepresentationRingBHistRepresentationPacket group ring reps directSum tensor provenance
        classifier ledger endpoint bundle pkg ->
      Cont reps directSum directSumEndpoint ->
        Cont reps tensor tensorEndpoint ->
          Cont endpoint reps inducedEndpoint ->
            UnaryHistory group ∧ UnaryHistory ring ∧ UnaryHistory reps ∧
              UnaryHistory directSum ∧ UnaryHistory tensor ∧ UnaryHistory ledger ∧
                UnaryHistory endpoint ∧ UnaryHistory directSumEndpoint ∧
                  UnaryHistory tensorEndpoint ∧ UnaryHistory inducedEndpoint ∧
                    hsame endpoint (append ledger tensor) ∧
                      hsame directSumEndpoint (append reps directSum) ∧
                        hsame tensorEndpoint (append reps tensor) ∧
                          hsame inducedEndpoint (append endpoint reps) ∧
                            PkgSig bundle endpoint pkg := by
  intro packet directSumRow tensorRow inducedRow
  have boundary :=
    RepresentationRingBHistRepresentationPacket_carrier_boundary packet
  have operationCoverage :=
    RepresentationRingBHistRepresentationPacket_operation_ledger_coverage packet directSumRow
      tensorRow
  have inducedCoverage :=
    RepresentationRingBHistRepresentationPacket_induced_consumer_boundary packet inducedRow
  constructor
  · exact boundary.left
  · constructor
    · exact boundary.right.left
    · constructor
      · exact boundary.right.right.left
      · constructor
        · exact boundary.right.right.right.left
        · constructor
          · exact boundary.right.right.right.right.left
          · constructor
            · exact boundary.right.right.right.right.right.right.right.left
            · constructor
              · exact boundary.right.right.right.right.right.right.right.right.left
              · constructor
                · exact operationCoverage.left
                · constructor
                  · exact operationCoverage.right.left
                  · constructor
                    · exact inducedCoverage.left
                    · constructor
                      · exact
                          boundary.right.right.right.right.right.right.right.right.right.right.left
                      · constructor
                        · exact operationCoverage.right.right.left
                        · constructor
                          · exact operationCoverage.right.right.right.left
                          · constructor
                            · exact inducedCoverage.right.left
                            · exact
                                boundary.right.right.right.right.right.right.right.right.right.right.right

end BEDC.Derived.RepresentationRingUp
