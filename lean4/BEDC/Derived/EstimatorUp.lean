import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EstimatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def EstimatorBHistSourceSurface [AskSetup] [PackageSetup]
    (samples independence estimator bias variance transport ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory samples ∧ UnaryHistory independence ∧ UnaryHistory bias ∧
    UnaryHistory variance ∧ UnaryHistory transport ∧ Cont samples independence estimator ∧
      Cont bias variance ledger ∧ Cont estimator ledger endpoint ∧ PkgSig bundle endpoint pkg

theorem EstimatorBHistSourceSurface_source_obligation [AskSetup] [PackageSetup]
    {samples independence estimator bias variance transport ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EstimatorBHistSourceSurface samples independence estimator bias variance transport ledger
        endpoint bundle pkg ->
      UnaryHistory samples ∧ UnaryHistory independence ∧ UnaryHistory estimator ∧
        UnaryHistory bias ∧ UnaryHistory variance ∧ UnaryHistory ledger ∧
          UnaryHistory endpoint ∧ Cont samples independence estimator ∧
            Cont bias variance ledger ∧ Cont estimator ledger endpoint ∧
              PkgSig bundle endpoint pkg := by
  intro surface
  have samplesUnary : UnaryHistory samples := surface.left
  have independenceUnary : UnaryHistory independence := surface.right.left
  have biasUnary : UnaryHistory bias := surface.right.right.left
  have varianceUnary : UnaryHistory variance := surface.right.right.right.left
  have estimatorRow : Cont samples independence estimator :=
    surface.right.right.right.right.right.left
  have ledgerRow : Cont bias variance ledger :=
    surface.right.right.right.right.right.right.left
  have endpointRow : Cont estimator ledger endpoint :=
    surface.right.right.right.right.right.right.right.left
  have estimatorUnary : UnaryHistory estimator :=
    unary_cont_closed samplesUnary independenceUnary estimatorRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed biasUnary varianceUnary ledgerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed estimatorUnary ledgerUnary endpointRow
  exact And.intro samplesUnary
    (And.intro independenceUnary
      (And.intro estimatorUnary
        (And.intro biasUnary
          (And.intro varianceUnary
            (And.intro ledgerUnary
              (And.intro endpointUnary
                (And.intro estimatorRow
                  (And.intro ledgerRow
                    (And.intro endpointRow
                      surface.right.right.right.right.right.right.right.right)))))))))

theorem EstimatorBHistSourceSurface_transport_obligation [AskSetup] [PackageSetup]
    {samples independence estimator bias variance transport ledger endpoint samples' independence'
      bias' variance' transport' estimator' ledger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EstimatorBHistSourceSurface samples independence estimator bias variance transport ledger
        endpoint bundle pkg ->
      hsame samples samples' ->
        hsame independence independence' ->
          hsame bias bias' ->
            hsame variance variance' ->
              hsame transport transport' ->
                Cont samples' independence' estimator' ->
                  Cont bias' variance' ledger' ->
                    Cont estimator' ledger' endpoint' ->
                      PkgSig bundle endpoint' pkg ->
                        EstimatorBHistSourceSurface samples' independence' estimator' bias'
                            variance' transport' ledger' endpoint' bundle pkg ∧
                          hsame estimator estimator' ∧ hsame ledger ledger' ∧
                            hsame endpoint endpoint' := by
  intro surface sameSamples sameIndependence sameBias sameVariance sameTransport
  intro estimatorRow' ledgerRow' endpointRow' pkgRow'
  have sourceRows := EstimatorBHistSourceSurface_source_obligation surface
  have samplesUnary' : UnaryHistory samples' :=
    unary_transport sourceRows.left sameSamples
  have independenceUnary' : UnaryHistory independence' :=
    unary_transport sourceRows.right.left sameIndependence
  have biasUnary' : UnaryHistory bias' :=
    unary_transport sourceRows.right.right.right.left sameBias
  have varianceUnary' : UnaryHistory variance' :=
    unary_transport sourceRows.right.right.right.right.left sameVariance
  have transportUnary' : UnaryHistory transport' :=
    unary_transport surface.right.right.right.right.left sameTransport
  have sameEstimator : hsame estimator estimator' :=
    cont_respects_hsame sameSamples sameIndependence
      sourceRows.right.right.right.right.right.right.right.left estimatorRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameBias sameVariance
      sourceRows.right.right.right.right.right.right.right.right.left ledgerRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameEstimator sameLedger
      sourceRows.right.right.right.right.right.right.right.right.right.left endpointRow'
  have transported :
      EstimatorBHistSourceSurface samples' independence' estimator' bias' variance'
        transport' ledger' endpoint' bundle pkg :=
    And.intro samplesUnary'
      (And.intro independenceUnary'
        (And.intro biasUnary'
          (And.intro varianceUnary'
            (And.intro transportUnary'
              (And.intro estimatorRow'
                (And.intro ledgerRow' (And.intro endpointRow' pkgRow')))))))
  exact And.intro transported
    (And.intro sameEstimator (And.intro sameLedger sameEndpoint))

end BEDC.Derived.EstimatorUp
