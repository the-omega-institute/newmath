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

theorem DiagonalLimitCompatibilityCarrier_root_selector_budget_exhaustion
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector locked endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal windows selector →
        Cont selector readback locked →
          Cont locked realSeal endpoint →
            PkgSig bundle endpoint pkg →
              UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory sealRow ∧
                UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                  UnaryHistory realSeal ∧ UnaryHistory selector ∧ UnaryHistory locked ∧
                    UnaryHistory endpoint ∧ Cont diagonal triangle sealRow ∧
                      Cont dyadic windows readback ∧ Cont diagonal windows selector ∧
                        Cont selector readback locked ∧ Cont locked realSeal endpoint ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle UnaryHistory
  intro carrier diagonalWindowsSelector selectorReadbackLocked lockedRealSealEndpoint
    endpointPkg
  obtain ⟨diagonalUnary, triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackLocked
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed lockedUnary realSealUnary lockedRealSealEndpoint
  exact
    ⟨diagonalUnary, triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
      readbackUnary, realSealUnary, selectorUnary, lockedUnary, endpointUnary,
      diagonalTriangleSeal, dyadicWindowsReadback, diagonalWindowsSelector,
      selectorReadbackLocked, lockedRealSealEndpoint, provenancePkg, endpointPkg⟩

theorem DiagonalLimitCompatibilityRootSelectorBudgetExhaustion [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selectorBudget : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal triangle selectorBudget ->
        PkgSig bundle selectorBudget pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row selectorBudget ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row diagonal ∨ hsame row triangle ∨ hsame row sealRow ∨
                  hsame row dyadic ∨ hsame row windows ∨ hsame row readback ∨
                    hsame row realSeal ∨ hsame row selectorBudget)
              (fun row : BHist =>
                hsame row selectorBudget ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle selectorBudget pkg)
              hsame ∧
            UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory sealRow ∧
              UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                UnaryHistory realSeal ∧ UnaryHistory selectorBudget := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier selectorRoute selectorBudgetPkg
  obtain ⟨diagonalUnary, triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorBudgetUnary : UnaryHistory selectorBudget :=
    unary_cont_closed diagonalUnary triangleUnary selectorRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row selectorBudget ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row diagonal ∨ hsame row triangle ∨ hsame row sealRow ∨
              hsame row dyadic ∨ hsame row windows ∨ hsame row readback ∨
                hsame row realSeal ∨ hsame row selectorBudget)
          (fun row : BHist =>
            hsame row selectorBudget ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle selectorBudget pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro selectorBudget ⟨hsame_refl selectorBudget, selectorBudgetUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, provenancePkg, selectorBudgetPkg⟩
  }
  exact
    ⟨cert, diagonalUnary, triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
      readbackUnary, realSealUnary, selectorBudgetUnary⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
