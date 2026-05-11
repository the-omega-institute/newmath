import BEDC.Derived.KKTUp

namespace BEDC.Derived.KKTUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Bundle
open BEDC.FKernel.Sig
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KKTPrimalDualCarrier_stationarity_feasibility_transport [AskSetup] [PackageSetup]
    {primal dual residual stationarity feasible slack ledger provenance primal' dual'
      residual' stationarity' feasible' slack' ledger' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KKTPrimalDualCarrier primal dual residual stationarity feasible slack ledger provenance
        bundle pkg ->
      hsame primal primal' -> hsame dual dual' -> hsame residual residual' ->
        hsame feasible feasible' -> hsame slack slack' ->
          Cont primal' residual' stationarity' ->
            Cont dual' slack' ledger' ->
              Cont stationarity' feasible' provenance' ->
                PkgSig bundle provenance' pkg ->
                  KKTPrimalDualCarrier primal' dual' residual' stationarity' feasible' slack'
                      ledger' provenance' bundle pkg ∧
                    hsame stationarity stationarity' ∧ hsame ledger ledger' ∧
                      hsame provenance provenance' := by
  intro carrier samePrimal sameDual sameResidual sameFeasible sameSlack
  intro stationarityRow' ledgerRow' provenanceRow' pkgSig'
  have primalUnary' : UnaryHistory primal' :=
    unary_transport carrier.left samePrimal
  have dualUnary' : UnaryHistory dual' :=
    unary_transport carrier.right.left sameDual
  have residualUnary' : UnaryHistory residual' :=
    unary_transport carrier.right.right.left sameResidual
  have feasibleUnary' : UnaryHistory feasible' :=
    unary_transport carrier.right.right.right.right.left sameFeasible
  have slackUnary' : UnaryHistory slack' :=
    unary_transport carrier.right.right.right.right.right.left sameSlack
  have sameStationarity : hsame stationarity stationarity' :=
    cont_respects_hsame samePrimal sameResidual
      carrier.right.right.right.right.right.right.right.right.left stationarityRow'
  have stationarityUnary' : UnaryHistory stationarity' :=
    unary_cont_closed primalUnary' residualUnary' stationarityRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameDual sameSlack
      carrier.right.right.right.right.right.right.right.right.right.left ledgerRow'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed dualUnary' slackUnary' ledgerRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameStationarity sameFeasible
      carrier.right.right.right.right.right.right.right.right.right.right.left provenanceRow'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed stationarityUnary' feasibleUnary' provenanceRow'
  exact
    And.intro
      (And.intro primalUnary'
        (And.intro dualUnary'
          (And.intro residualUnary'
            (And.intro stationarityUnary'
              (And.intro feasibleUnary'
                (And.intro slackUnary'
                  (And.intro ledgerUnary'
                    (And.intro provenanceUnary'
                      (And.intro stationarityRow'
                        (And.intro ledgerRow' (And.intro provenanceRow' pkgSig')))))))))))
      (And.intro sameStationarity (And.intro sameLedger sameProvenance))

end BEDC.Derived.KKTUp
