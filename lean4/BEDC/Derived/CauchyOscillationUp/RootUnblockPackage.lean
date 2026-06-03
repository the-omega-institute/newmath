import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationRootUnblockPackage [AskSetup] [PackageSetup]
    {tailWindow modulus tolerance ledger sealRow transport routes provenance nameCert thresholdRead
      ledgerRead sealRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes provenance
        nameCert bundle pkg →
      Cont tailWindow modulus thresholdRead →
        Cont thresholdRead tolerance ledgerRead →
          Cont ledgerRead sealRow sealRead →
            Cont sealRead transport replayRead →
              PkgSig bundle replayRead pkg →
                UnaryHistory thresholdRead ∧ UnaryHistory ledgerRead ∧
                  UnaryHistory sealRead ∧ UnaryHistory replayRead ∧
                    Cont tailWindow modulus thresholdRead ∧
                      Cont thresholdRead tolerance ledgerRead ∧
                        Cont ledgerRead sealRow sealRead ∧
                          Cont sealRead transport replayRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier thresholdRoute ledgerRoute sealRoute replayRoute replayPkg
  obtain ⟨tailWindowUnary, modulusUnary, toleranceUnary, _ledgerUnary, sealUnary,
    transportUnary, _routesUnary, _provenanceUnary, _nameCertUnary, _tailWindowModulus,
    _modulusTolerance, _ledgerSeal, _routesNameCert, provenancePkg⟩ := carrier
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed tailWindowUnary modulusUnary thresholdRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed thresholdUnary toleranceUnary ledgerRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed ledgerReadUnary sealUnary sealRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed sealReadUnary transportUnary replayRoute
  exact
    ⟨thresholdUnary, ledgerReadUnary, sealReadUnary, replayReadUnary, thresholdRoute,
      ledgerRoute, sealRoute, replayRoute, provenancePkg, replayPkg⟩

end BEDC.Derived.CauchyOscillationUp
