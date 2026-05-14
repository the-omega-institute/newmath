import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCompletionBoundary [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      aligned gate completion terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont triangle dyadic aligned ->
        Cont aligned windows gate ->
          Cont gate readback completion ->
            Cont completion realSeal terminal ->
              PkgSig bundle terminal pkg ->
                UnaryHistory triangle ∧ UnaryHistory dyadic ∧ UnaryHistory aligned ∧
                  UnaryHistory windows ∧ UnaryHistory gate ∧ UnaryHistory readback ∧
                    UnaryHistory completion ∧ UnaryHistory realSeal ∧ UnaryHistory terminal ∧
                      Cont triangle dyadic aligned ∧ Cont aligned windows gate ∧
                        Cont gate readback completion ∧ Cont completion realSeal terminal ∧
                          Cont route cert transport ∧ PkgSig bundle provenance pkg ∧
                            PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier triangleDyadicAligned alignedWindowsGate gateReadbackCompletion
    completionRealSealTerminal terminalPkg
  obtain ⟨_diagonalUnary, triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary,
    _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    routeCertTransport, provenancePkg⟩ := carrier
  have alignedUnary : UnaryHistory aligned :=
    unary_cont_closed triangleUnary dyadicUnary triangleDyadicAligned
  have gateUnary : UnaryHistory gate :=
    unary_cont_closed alignedUnary windowsUnary alignedWindowsGate
  have completionUnary : UnaryHistory completion :=
    unary_cont_closed gateUnary readbackUnary gateReadbackCompletion
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed completionUnary realSealUnary completionRealSealTerminal
  exact
    ⟨triangleUnary, dyadicUnary, alignedUnary, windowsUnary, gateUnary, readbackUnary,
      completionUnary, realSealUnary, terminalUnary, triangleDyadicAligned,
      alignedWindowsGate, gateReadbackCompletion, completionRealSealTerminal,
      routeCertTransport, provenancePkg, terminalPkg⟩

theorem DiagonalLimitCompatibilitySourceRouteExactness [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      sealBudget windowRead terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont sealRow dyadic sealBudget ->
        Cont sealBudget windows windowRead ->
          Cont windowRead readback terminal ->
            PkgSig bundle terminal pkg ->
              UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory sealRow ∧
                UnaryHistory dyadic ∧ UnaryHistory sealBudget ∧ UnaryHistory windows ∧
                  UnaryHistory windowRead ∧ UnaryHistory readback ∧ UnaryHistory terminal ∧
                    Cont diagonal triangle sealRow ∧ Cont sealRow dyadic sealBudget ∧
                      Cont sealBudget windows windowRead ∧ Cont windowRead readback terminal ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier sealRowDyadicSealBudget sealBudgetWindowsWindowRead
    windowReadReadbackTerminal terminalPkg
  obtain ⟨diagonalUnary, triangleUnary, sealRowUnary, dyadicUnary, windowsUnary, readbackUnary,
    _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary,
    diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed sealRowUnary dyadicUnary sealRowDyadicSealBudget
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed sealBudgetUnary windowsUnary sealBudgetWindowsWindowRead
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed windowReadUnary readbackUnary windowReadReadbackTerminal
  exact
    ⟨diagonalUnary, triangleUnary, sealRowUnary, dyadicUnary, sealBudgetUnary, windowsUnary,
      windowReadUnary, readbackUnary, terminalUnary, diagonalTriangleSeal,
      sealRowDyadicSealBudget, sealBudgetWindowsWindowRead, windowReadReadbackTerminal,
      provenancePkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
