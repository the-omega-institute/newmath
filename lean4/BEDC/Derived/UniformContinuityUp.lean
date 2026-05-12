import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def UniformContinuityCarrier [AskSetup] [PackageSetup]
    (source target graph tolerance probes centers radii coverage lowerLedger triangleRows
      transports localCert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧ UnaryHistory tolerance ∧
    UnaryHistory centers ∧ UnaryHistory radii ∧ UnaryHistory lowerLedger ∧
      UnaryHistory coverage ∧ UnaryHistory triangleRows ∧ UnaryHistory transports ∧
        UnaryHistory localCert ∧
          (∀ probe : ProbeName, InBundle probe bundle -> UnaryHistory probes) ∧
            Cont centers radii coverage ∧ Cont coverage lowerLedger triangleRows ∧
              Cont triangleRows transports localCert ∧ PkgSig bundle endpoint pkg ∧
                hsame endpoint (append transports localCert)

theorem UniformContinuityCarrier_finite_net_modulus_fold [AskSetup] [PackageSetup]
    {source target graph tolerance probes centers radii coverage lowerLedger triangleRows
      transports localCert endpoint foldedPrecision : BHist}
    {probe : ProbeName} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformContinuityCarrier source target graph tolerance probes centers radii coverage
        lowerLedger triangleRows transports localCert endpoint bundle pkg ->
      InBundle probe bundle ->
        Cont radii lowerLedger foldedPrecision ->
          UnaryHistory foldedPrecision ∧ PkgSig bundle endpoint pkg ∧
            hsame endpoint (append transports localCert) := by
  intro carrier member foldedRoute
  obtain ⟨_sourceUnary, _targetUnary, _graphUnary, _toleranceUnary, _centersUnary,
    radiiUnary, lowerLedgerUnary, _coverageUnary, _triangleRowsUnary, _transportsUnary,
    _localCertUnary, probeRows, _centersRadiiCoverage, _coverageLowerTriangle,
    _triangleTransportLocal, endpointPkg, endpointSame⟩ := carrier
  have _probeRowUnary : UnaryHistory probes := probeRows probe member
  have foldedUnary : UnaryHistory foldedPrecision :=
    unary_cont_closed radiiUnary lowerLedgerUnary foldedRoute
  exact ⟨foldedUnary, endpointPkg, endpointSame⟩

end BEDC.Derived.UniformContinuityUp
