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

theorem DiagonalLimitCompatibilityBudgetSelectorRoute [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector selectedWindow selectedRead selectedSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic selector ->
        Cont selector windows selectedWindow ->
          Cont selectedWindow readback selectedRead ->
            Cont selectedRead realSeal selectedSeal ->
              PkgSig bundle selectedSeal pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row selectedSeal ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row selector ∨ hsame row selectedWindow ∨
                        hsame row selectedRead ∨ hsame row selectedSeal)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont diagonal dyadic selector ∧
                        Cont selector windows selectedWindow ∧
                          Cont selectedWindow readback selectedRead ∧
                            Cont selectedRead realSeal selectedSeal ∧
                              PkgSig bundle selectedSeal pkg)
                    hsame ∧
                  UnaryHistory selector ∧ UnaryHistory selectedWindow ∧
                    UnaryHistory selectedRead ∧ UnaryHistory selectedSeal ∧
                      PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier diagonalDyadicSelector selectorWindowsSelectedWindow
    selectedWindowReadbackSelectedRead selectedReadRealSealSelectedSeal selectedSealPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicSelector
  have selectedWindowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed selectorUnary windowsUnary selectorWindowsSelectedWindow
  have selectedReadUnary : UnaryHistory selectedRead :=
    unary_cont_closed selectedWindowUnary readbackUnary selectedWindowReadbackSelectedRead
  have selectedSealUnary : UnaryHistory selectedSeal :=
    unary_cont_closed selectedReadUnary realSealUnary selectedReadRealSealSelectedSeal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row selectedSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row selector ∨ hsame row selectedWindow ∨ hsame row selectedRead ∨
              hsame row selectedSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont diagonal dyadic selector ∧
              Cont selector windows selectedWindow ∧ Cont selectedWindow readback selectedRead ∧
                Cont selectedRead realSeal selectedSeal ∧ PkgSig bundle selectedSeal pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro selectedSeal ⟨hsame_refl selectedSeal, selectedSealUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, diagonalDyadicSelector, selectorWindowsSelectedWindow,
          selectedWindowReadbackSelectedRead, selectedReadRealSealSelectedSeal,
          selectedSealPkg⟩
  }
  exact
    ⟨cert, selectorUnary, selectedWindowUnary, selectedReadUnary, selectedSealUnary,
      provenancePkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
