import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootRouteSelectorMinimality [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetSource meshRead selectorWindow regularRead sealRead terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal dyadic budgetSource →
        Cont budgetSource triangle meshRead →
          Cont meshRead windows selectorWindow →
            Cont selectorWindow readback regularRead →
              Cont regularRead realSeal sealRead →
                Cont sealRead cert terminal →
                  PkgSig bundle terminal pkg →
                    UnaryHistory budgetSource ∧ UnaryHistory meshRead ∧
                      UnaryHistory selectorWindow ∧ UnaryHistory regularRead ∧
                        UnaryHistory sealRead ∧ UnaryHistory terminal ∧
                          Cont diagonal dyadic budgetSource ∧
                            Cont budgetSource triangle meshRead ∧
                              Cont meshRead windows selectorWindow ∧
                                Cont selectorWindow readback regularRead ∧
                                  Cont regularRead realSeal sealRead ∧
                                    Cont sealRead cert terminal ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier diagonalDyadicBudget budgetTriangleMesh meshWindowsSelector
    selectorReadbackRegular regularRealSeal sealCertTerminal terminalPkg
  obtain ⟨diagonalUnary, triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetUnary : UnaryHistory budgetSource :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicBudget
  have meshUnary : UnaryHistory meshRead :=
    unary_cont_closed budgetUnary triangleUnary budgetTriangleMesh
  have selectorUnary : UnaryHistory selectorWindow :=
    unary_cont_closed meshUnary windowsUnary meshWindowsSelector
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackRegular
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary realSealUnary regularRealSeal
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed sealUnary certUnary sealCertTerminal
  exact
    ⟨budgetUnary, meshUnary, selectorUnary, regularUnary, sealUnary, terminalUnary,
      diagonalDyadicBudget, budgetTriangleMesh, meshWindowsSelector,
      selectorReadbackRegular, regularRealSeal, sealCertTerminal, provenancePkg,
      terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
