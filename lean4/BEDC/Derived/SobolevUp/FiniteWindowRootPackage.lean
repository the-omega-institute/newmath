import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_finite_window_root_package [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert
      finiteWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg ->
      Cont domain magnitude finiteWindow ->
        PkgSig bundle finiteWindow pkg ->
          UnaryHistory domain ∧ UnaryHistory base ∧ UnaryHistory codomain ∧
            UnaryHistory magnitude ∧ UnaryHistory gradient ∧ UnaryHistory finiteWindow ∧
              Cont domain base codomain ∧ Cont codomain magnitude gradient ∧
                Cont domain magnitude finiteWindow ∧ Cont gradient transports routes ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle finiteWindow pkg := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier finiteWindowRoute finiteWindowPkg
  obtain ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, gradientTransportsRoutes, _routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have finiteWindowUnary : UnaryHistory finiteWindow :=
    unary_cont_closed domainUnary magnitudeUnary finiteWindowRoute
  exact
    ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary,
      finiteWindowUnary, domainBaseCodomain, codomainMagnitudeGradient, finiteWindowRoute,
      gradientTransportsRoutes, provenancePkg, finiteWindowPkg⟩

end BEDC.Derived.SobolevUp
