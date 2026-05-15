import BEDC.Derived.DiagonallimitcompatibilityUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_root_provenance_exhaustion [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetRoot budgetWindow budgetRead budgetSeal terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic budgetRoot ->
        Cont budgetRoot windows budgetWindow ->
          Cont budgetWindow readback budgetRead ->
            Cont budgetRead realSeal budgetSeal ->
              Cont route cert terminal ->
                PkgSig bundle budgetSeal pkg ->
                  PkgSig bundle terminal pkg ->
                    SemanticNameCert
                      (fun row : BHist =>
                        DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic
                          windows readback realSeal transport route provenance cert bundle pkg ∧
                          hsame row terminal)
                      (fun row : BHist =>
                        Cont diagonal dyadic budgetRoot ∧
                          Cont budgetRoot windows budgetWindow ∧
                            Cont budgetWindow readback budgetRead ∧
                              Cont budgetRead realSeal budgetSeal ∧ Cont route cert row)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle budgetSeal pkg ∧ PkgSig bundle terminal pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle PkgSig SemanticNameCert
  intro carrier diagonalDyadicRoot rootWindowsBudget budgetWindowReadback
    budgetReadRealSeal routeCertTerminal budgetSealPkg terminalPkg
  have carrierWitness := carrier
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, _windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, routeUnary, _provenanceUnary, certUnary,
    _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed routeUnary certUnary routeCertTerminal
  exact {
    core := {
      carrier_inhabited := Exists.intro terminal
        (And.intro carrierWitness (hsame_refl terminal))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact
        ⟨diagonalDyadicRoot, rootWindowsBudget, budgetWindowReadback, budgetReadRealSeal,
          cont_result_hsame_transport routeCertTerminal (hsame_symm source.right)⟩
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport terminalUnary (hsame_symm source.right), provenancePkg, budgetSealPkg,
          terminalPkg⟩
  }

end BEDC.Derived.DiagonallimitcompatibilityUp
