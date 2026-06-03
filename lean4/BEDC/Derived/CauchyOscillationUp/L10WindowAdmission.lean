import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationL10WindowAdmission [AskSetup] [PackageSetup]
    {tailWindow modulus tolerance ledger sealRow transport routes provenance nameCert l10Window
      ledgerRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes provenance
        nameCert bundle pkg ->
      Cont tailWindow tolerance l10Window ->
        Cont l10Window modulus ledgerRead ->
          Cont ledgerRead sealRow sealRead ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory l10Window ∧ UnaryHistory ledgerRead ∧ UnaryHistory sealRead ∧
                hsame sealRead (append ledgerRead sealRow) ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont ProbeBundle Pkg hsame UnaryHistory
  intro carrier windowRoute ledgerRoute sealRoute sealPkg
  obtain ⟨tailWindowUnary, modulusUnary, toleranceUnary, _ledgerUnary, sealUnary,
    _transportUnary, _routesUnary, _provenanceUnary, _nameCertUnary, _tailWindowModulus,
    _modulusTolerance, _ledgerSeal, _routesNameCert, _carrierPkg⟩ := carrier
  have l10WindowUnary : UnaryHistory l10Window :=
    unary_cont_closed tailWindowUnary toleranceUnary windowRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed l10WindowUnary modulusUnary ledgerRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed ledgerReadUnary sealUnary sealRoute
  have sealEndpoint : hsame sealRead (append ledgerRead sealRow) := sealRoute
  exact ⟨l10WindowUnary, ledgerReadUnary, sealReadUnary, sealEndpoint, sealPkg⟩

end BEDC.Derived.CauchyOscillationUp
