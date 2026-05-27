import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_bhist_carrier_scope [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert
      scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg →
      Cont domain provenance scopedRead →
        PkgSig bundle scopedRead pkg →
          UnaryHistory domain ∧ UnaryHistory base ∧ UnaryHistory codomain ∧
            UnaryHistory magnitude ∧ UnaryHistory gradient ∧ UnaryHistory transports ∧
              UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
                UnaryHistory scopedRead ∧ Cont domain base codomain ∧
                  Cont codomain magnitude gradient ∧ Cont gradient transports routes ∧
                    Cont routes provenance localCert ∧ Cont domain provenance scopedRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle scopedRead pkg := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier domainProvenanceRead scopedPkg
  obtain ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary,
    transportsUnary, routesUnary, provenanceUnary, localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, gradientTransportsRoutes, routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed domainUnary provenanceUnary domainProvenanceRead
  exact
    ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary,
      transportsUnary, routesUnary, provenanceUnary, localCertUnary, scopedUnary,
      domainBaseCodomain, codomainMagnitudeGradient, gradientTransportsRoutes,
      routesProvenanceLocalCert, domainProvenanceRead, provenancePkg, scopedPkg⟩

end BEDC.Derived.SobolevUp
