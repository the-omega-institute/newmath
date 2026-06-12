import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevFiniteEnergyObligationScope [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert energyRead
      scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg ->
      Cont magnitude gradient energyRead ->
        Cont energyRead provenance scopeRead ->
          PkgSig bundle scopeRead pkg ->
            UnaryHistory domain ∧ UnaryHistory base ∧ UnaryHistory codomain ∧
              UnaryHistory magnitude ∧ UnaryHistory gradient ∧ UnaryHistory energyRead ∧
                UnaryHistory scopeRead ∧ Cont domain base codomain ∧
                  Cont codomain magnitude gradient ∧ Cont magnitude gradient energyRead ∧
                    Cont energyRead provenance scopeRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle scopeRead pkg := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier magnitudeGradientEnergy energyProvenanceScope scopePkg
  obtain ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary,
    _transportsUnary, _routesUnary, provenanceUnary, _localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, _gradientTransportsRoutes, _routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have energyUnary : UnaryHistory energyRead :=
    unary_cont_closed magnitudeUnary gradientUnary magnitudeGradientEnergy
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed energyUnary provenanceUnary energyProvenanceScope
  exact
    ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary, energyUnary,
      scopeUnary, domainBaseCodomain, codomainMagnitudeGradient, magnitudeGradientEnergy,
      energyProvenanceScope, provenancePkg, scopePkg⟩

end BEDC.Derived.SobolevUp
