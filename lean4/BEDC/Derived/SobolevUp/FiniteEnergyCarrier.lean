import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_finite_energy_carrier [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert
      energyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg →
      Cont (append (append domain magnitude) gradient) transports energyRead →
        PkgSig bundle energyRead pkg →
          UnaryHistory energyRead ∧
            hsame energyRead (append (append (append domain magnitude) gradient) transports) ∧
              Cont domain base codomain ∧
                Cont codomain magnitude gradient ∧
                  Cont gradient transports routes ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle energyRead pkg := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist hsame ProbeBundle Pkg Cont UnaryHistory
  intro carrier finiteEnergy energyPkg
  obtain ⟨domainUnary, _baseUnary, _codomainUnary, magnitudeUnary, gradientUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, gradientTransportsRoutes, _routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have domainMagnitudeUnary : UnaryHistory (append domain magnitude) :=
    unary_append_closed domainUnary magnitudeUnary
  have domainMagnitudeGradientUnary :
      UnaryHistory (append (append domain magnitude) gradient) :=
    unary_append_closed domainMagnitudeUnary gradientUnary
  have energyUnary : UnaryHistory energyRead :=
    unary_cont_closed domainMagnitudeGradientUnary transportsUnary finiteEnergy
  exact
    ⟨energyUnary, finiteEnergy, domainBaseCodomain, codomainMagnitudeGradient,
      gradientTransportsRoutes, provenancePkg, energyPkg⟩

end BEDC.Derived.SobolevUp
