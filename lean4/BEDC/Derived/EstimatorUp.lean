import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EstimatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem EstimatorBHistSourceSurface_namecert_obligation_surface [AskSetup] [PackageSetup]
    {samples independence estimator bias variance transport ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EstimatorBHistSourceSurface samples independence estimator bias variance transport ledger
        endpoint bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint) hsame ∧
        UnaryHistory samples ∧ UnaryHistory independence ∧ UnaryHistory estimator ∧
          UnaryHistory bias ∧ UnaryHistory variance ∧ UnaryHistory ledger ∧
            UnaryHistory endpoint ∧ Cont samples independence estimator ∧
              Cont bias variance ledger ∧ Cont estimator ledger endpoint ∧
                PkgSig bundle endpoint pkg := by
  intro surface
  have cert :
      SemanticNameCert (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint) hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint (hsame_refl endpoint)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row other target sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other sameRows rowSource
        exact hsame_trans (hsame_symm sameRows) rowSource
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert (EstimatorBHistSourceSurface_source_obligation surface)

theorem EstimatorBHistSourceSurface_finite_sample_boundary [AskSetup] [PackageSetup]
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
                          UnaryHistory estimator' ∧ UnaryHistory ledger' ∧
                            UnaryHistory endpoint' ∧ hsame estimator estimator' ∧
                              hsame ledger ledger' ∧ hsame endpoint endpoint' := by
  intro surface sameSamples sameIndependence sameBias sameVariance sameTransport
  intro estimatorRow' ledgerRow' endpointRow' pkgRow'
  have transported :=
    EstimatorBHistSourceSurface_transport_obligation surface sameSamples sameIndependence
      sameBias sameVariance sameTransport estimatorRow' ledgerRow' endpointRow' pkgRow'
  have sourceRows' := EstimatorBHistSourceSurface_source_obligation transported.left
  exact And.intro transported.left
    (And.intro sourceRows'.right.right.left
      (And.intro sourceRows'.right.right.right.right.right.left
          (And.intro sourceRows'.right.right.right.right.right.right.left
            (And.intro transported.right.left
              (And.intro transported.right.right.left transported.right.right.right)))))

theorem EstimatorBHistSourceSurface_finite_cont_readback_determinacy [AskSetup]
    [PackageSetup]
    {samples independence estimator bias variance transport ledger endpoint samples'
      independence' estimator' bias' variance' transport' ledger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EstimatorBHistSourceSurface samples independence estimator bias variance transport ledger
        endpoint bundle pkg ->
      EstimatorBHistSourceSurface samples' independence' estimator' bias' variance'
          transport' ledger' endpoint' bundle pkg ->
        hsame samples samples' ->
          hsame independence independence' ->
            hsame bias bias' ->
              hsame variance variance' ->
                hsame transport transport' ->
                  hsame estimator estimator' ∧ hsame ledger ledger' ∧
                    hsame endpoint endpoint' ∧ PkgSig bundle endpoint pkg ∧
                      PkgSig bundle endpoint' pkg := by
  intro surface surface' sameSamples sameIndependence sameBias sameVariance _sameTransport
  have source := EstimatorBHistSourceSurface_source_obligation surface
  have source' := EstimatorBHistSourceSurface_source_obligation surface'
  have sameEstimator : hsame estimator estimator' :=
    cont_respects_hsame sameSamples sameIndependence
      source.right.right.right.right.right.right.right.left
      source'.right.right.right.right.right.right.right.left
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameBias sameVariance
      source.right.right.right.right.right.right.right.right.left
      source'.right.right.right.right.right.right.right.right.left
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameEstimator sameLedger
      source.right.right.right.right.right.right.right.right.right.left
      source'.right.right.right.right.right.right.right.right.right.left
  exact And.intro sameEstimator
      (And.intro sameLedger
        (And.intro sameEndpoint
          (And.intro source.right.right.right.right.right.right.right.right.right.right
            source'.right.right.right.right.right.right.right.right.right.right)))

theorem EstimatorBHistSourceSurface_bias_variance_ledger_exclusion [AskSetup] [PackageSetup]
    {samples independence estimator bias variance transport ledger endpoint biasWitness
      varianceWitness : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EstimatorBHistSourceSurface samples independence estimator bias variance transport ledger
        endpoint bundle pkg ->
      Cont bias ledger biasWitness ->
        Cont variance ledger varianceWitness ->
          UnaryHistory biasWitness ∧ UnaryHistory varianceWitness ∧
            hsame biasWitness (append bias ledger) ∧
              hsame varianceWitness (append variance ledger) ∧ PkgSig bundle endpoint pkg := by
  intro surface biasRow varianceRow
  have sourceRows := EstimatorBHistSourceSurface_source_obligation surface
  have biasWitnessUnary : UnaryHistory biasWitness :=
    unary_cont_closed sourceRows.right.right.right.left
      sourceRows.right.right.right.right.right.left biasRow
  have varianceWitnessUnary : UnaryHistory varianceWitness :=
    unary_cont_closed sourceRows.right.right.right.right.left
      sourceRows.right.right.right.right.right.left varianceRow
  exact And.intro biasWitnessUnary
    (And.intro varianceWitnessUnary
      (And.intro biasRow
        (And.intro varianceRow
          sourceRows.right.right.right.right.right.right.right.right.right.right)))

end BEDC.Derived.EstimatorUp
