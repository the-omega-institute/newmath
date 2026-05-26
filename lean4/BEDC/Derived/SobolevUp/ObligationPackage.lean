import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_obligation_package [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert
      packageRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg →
      Cont routes localCert packageRead →
        PkgSig bundle packageRead pkg →
          UnaryHistory domain ∧
            UnaryHistory base ∧
              UnaryHistory codomain ∧
                UnaryHistory magnitude ∧
                  UnaryHistory gradient ∧
                    UnaryHistory transports ∧
                      UnaryHistory routes ∧
                        UnaryHistory localCert ∧
                          UnaryHistory packageRead ∧
                            Cont domain base codomain ∧
                              Cont codomain magnitude gradient ∧
                                Cont gradient transports routes ∧
                                  Cont routes provenance localCert ∧
                                    Cont routes localCert packageRead ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle packageRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier routesLocalPackage packagePkg
  obtain ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary,
    transportsUnary, routesUnary, _provenanceUnary, localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, gradientTransportsRoutes, routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have packageUnary : UnaryHistory packageRead :=
    unary_cont_closed routesUnary localCertUnary routesLocalPackage
  exact
    ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary, transportsUnary,
      routesUnary, localCertUnary, packageUnary, domainBaseCodomain, codomainMagnitudeGradient,
      gradientTransportsRoutes, routesProvenanceLocalCert, routesLocalPackage, provenancePkg,
      packagePkg⟩

end BEDC.Derived.SobolevUp
