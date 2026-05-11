import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.StatManifoldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def StatManifoldCarrier [AskSetup] [PackageSetup]
    (manifold fisher theta distribution metric primal dual provenance ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory manifold ∧ UnaryHistory fisher ∧ UnaryHistory theta ∧
    UnaryHistory distribution ∧ UnaryHistory metric ∧ UnaryHistory primal ∧
      UnaryHistory dual ∧ UnaryHistory provenance ∧ UnaryHistory ledger ∧
        Cont theta distribution metric ∧ Cont metric primal dual ∧
          Cont manifold fisher provenance ∧ Cont provenance dual ledger ∧
            PkgSig bundle ledger pkg

theorem StatManifoldCarrier_classifier_transport [AskSetup] [PackageSetup]
    {manifold fisher theta distribution metric primal dual provenance ledger manifold' fisher'
      theta' distribution' metric' primal' dual' provenance' ledger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StatManifoldCarrier manifold fisher theta distribution metric primal dual provenance ledger
        bundle pkg ->
      hsame manifold manifold' ->
        hsame fisher fisher' ->
          hsame theta theta' ->
            hsame distribution distribution' ->
              hsame primal primal' ->
                Cont theta' distribution' metric' ->
                  Cont metric' primal' dual' ->
                    Cont manifold' fisher' provenance' ->
                      Cont provenance' dual' ledger' ->
                        PkgSig bundle ledger' pkg ->
                          StatManifoldCarrier manifold' fisher' theta' distribution' metric' primal'
                              dual' provenance' ledger' bundle pkg ∧
                            hsame metric metric' ∧ hsame dual dual' ∧
                              hsame provenance provenance' ∧ hsame ledger ledger' := by
  intro carrier sameManifold sameFisher sameTheta sameDistribution samePrimal metricRow'
    dualRow' provenanceRow' ledgerRow' pkgSig'
  have manifoldUnary' : UnaryHistory manifold' :=
    unary_transport carrier.left sameManifold
  have fisherUnary' : UnaryHistory fisher' :=
    unary_transport carrier.right.left sameFisher
  have thetaUnary' : UnaryHistory theta' :=
    unary_transport carrier.right.right.left sameTheta
  have distributionUnary' : UnaryHistory distribution' :=
    unary_transport carrier.right.right.right.left sameDistribution
  have metricUnary' : UnaryHistory metric' :=
    unary_cont_closed thetaUnary' distributionUnary' metricRow'
  have primalUnary' : UnaryHistory primal' :=
    unary_transport carrier.right.right.right.right.right.left samePrimal
  have dualUnary' : UnaryHistory dual' :=
    unary_cont_closed metricUnary' primalUnary' dualRow'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed manifoldUnary' fisherUnary' provenanceRow'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed provenanceUnary' dualUnary' ledgerRow'
  have sameMetric : hsame metric metric' :=
    cont_respects_hsame sameTheta sameDistribution
      carrier.right.right.right.right.right.right.right.right.right.left metricRow'
  have sameDual : hsame dual dual' :=
    cont_respects_hsame sameMetric samePrimal
      carrier.right.right.right.right.right.right.right.right.right.right.left dualRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameManifold sameFisher
      carrier.right.right.right.right.right.right.right.right.right.right.right.left provenanceRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameProvenance sameDual
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.left ledgerRow'
  constructor
  · exact
      And.intro manifoldUnary'
        (And.intro fisherUnary'
          (And.intro thetaUnary'
            (And.intro distributionUnary'
              (And.intro metricUnary'
                (And.intro primalUnary'
                  (And.intro dualUnary'
                    (And.intro provenanceUnary'
                      (And.intro ledgerUnary'
                        (And.intro metricRow'
                          (And.intro dualRow'
                            (And.intro provenanceRow'
                              (And.intro ledgerRow' pkgSig'))))))))))))
  · exact And.intro sameMetric (And.intro sameDual (And.intro sameProvenance sameLedger))

end BEDC.Derived.StatManifoldUp
