import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootRouteBudgetTerminalExhaustion [AskSetup]
    [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance
      cert budgetPrefix sealBudget endpoint terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont dyadic windows budgetPrefix ->
        Cont budgetPrefix sealRow sealBudget ->
          Cont readback realSeal endpoint ->
            Cont endpoint cert terminal ->
              PkgSig bundle sealBudget pkg ->
                PkgSig bundle terminal pkg ->
                  UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory budgetPrefix ∧
                    UnaryHistory sealRow ∧ UnaryHistory sealBudget ∧ UnaryHistory readback ∧
                      UnaryHistory realSeal ∧ UnaryHistory endpoint ∧ UnaryHistory cert ∧
                        UnaryHistory terminal ∧ Cont dyadic windows budgetPrefix ∧
                          Cont budgetPrefix sealRow sealBudget ∧
                            Cont readback realSeal endpoint ∧ Cont endpoint cert terminal ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle sealBudget pkg ∧
                                  PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier dyadicWindowsBudgetPrefix budgetPrefixSealBudget readbackRealSealEndpoint
    endpointCertTerminal sealBudgetPkg terminalPkg
  obtain ⟨_diagonalUnary, _triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetPrefixUnary : UnaryHistory budgetPrefix :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsBudgetPrefix
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed budgetPrefixUnary sealRowUnary budgetPrefixSealBudget
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealEndpoint
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed endpointUnary certUnary endpointCertTerminal
  exact
    ⟨dyadicUnary, windowsUnary, budgetPrefixUnary, sealRowUnary, sealBudgetUnary,
      readbackUnary, realSealUnary, endpointUnary, certUnary, terminalUnary,
      dyadicWindowsBudgetPrefix, budgetPrefixSealBudget, readbackRealSealEndpoint,
      endpointCertTerminal, provenancePkg, sealBudgetPkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
