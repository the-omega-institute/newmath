import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyOscillationUniformLimitSource [AskSetup] [PackageSetup]
    (tailWindow modulus tolerance ledger transport routes provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont ProbeBundle PkgSig UnaryHistory
  UnaryHistory tailWindow ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
    UnaryHistory ledger ∧ UnaryHistory transport ∧ UnaryHistory routes ∧
      UnaryHistory provenance ∧ UnaryHistory nameCert ∧
        Cont tailWindow modulus tolerance ∧ Cont modulus tolerance ledger ∧
          Cont routes nameCert provenance ∧ PkgSig bundle provenance pkg

theorem CauchyOscillationUniformLimitSource_carrier_projection [AskSetup] [PackageSetup]
    {tailWindow modulus tolerance ledger sealRow transport routes provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes provenance
        nameCert bundle pkg ->
      CauchyOscillationUniformLimitSource tailWindow modulus tolerance ledger transport routes
        provenance nameCert bundle pkg := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier
  obtain ⟨tailWindowUnary, modulusUnary, toleranceUnary, ledgerUnary, _sealUnary,
    transportUnary, routesUnary, provenanceUnary, nameCertUnary, tailWindowModulus,
    modulusTolerance, _ledgerSeal, routesNameCert, provenancePkg⟩ := carrier
  exact
    ⟨tailWindowUnary, modulusUnary, toleranceUnary, ledgerUnary, transportUnary,
      routesUnary, provenanceUnary, nameCertUnary, tailWindowModulus, modulusTolerance,
      routesNameCert, provenancePkg⟩

end BEDC.Derived.CauchyOscillationUp
