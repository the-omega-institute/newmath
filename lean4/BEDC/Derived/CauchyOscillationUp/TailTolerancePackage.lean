import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationTailTolerancePackage [AskSetup] [PackageSetup]
    {tailWindow modulus tolerance ledger sealRow transport routes provenance nameCert
      toleranceRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes
        provenance nameCert bundle pkg →
      Cont tailWindow modulus toleranceRead →
        Cont toleranceRead ledger sealRead →
          PkgSig bundle sealRead pkg →
            UnaryHistory tailWindow ∧ UnaryHistory modulus ∧ UnaryHistory toleranceRead ∧
              UnaryHistory ledger ∧ UnaryHistory sealRead ∧
                Cont tailWindow modulus toleranceRead ∧ Cont toleranceRead ledger sealRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier toleranceRoute sealRoute sealPkg
  obtain ⟨tailWindowUnary, modulusUnary, _toleranceUnary, ledgerUnary, _sealUnary,
    _transportUnary, _routesUnary, _provenanceUnary, _nameCertUnary, _tailWindowModulus,
    _modulusTolerance, _ledgerSeal, _routesNameCert, provenancePkg⟩ := carrier
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed tailWindowUnary modulusUnary toleranceRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceReadUnary ledgerUnary sealRoute
  exact
    ⟨tailWindowUnary, modulusUnary, toleranceReadUnary, ledgerUnary, sealReadUnary,
      toleranceRoute, sealRoute, provenancePkg, sealPkg⟩

end BEDC.Derived.CauchyOscillationUp
