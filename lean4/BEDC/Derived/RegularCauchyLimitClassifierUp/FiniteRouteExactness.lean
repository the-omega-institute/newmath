import BEDC.Derived.RegularCauchyLimitClassifierUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RegularCauchyLimitClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyLimitClassifierFiniteRouteExactness [AskSetup] [PackageSetup]
    {input modulus diagonal window readback ledger sealRow transports routes provenance name
      budgetWindow budgetReadback exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitClassifierCarrier input modulus diagonal window readback ledger sealRow
        transports routes provenance name bundle pkg ->
      Cont window ledger budgetWindow ->
        Cont budgetWindow readback budgetReadback ->
          Cont budgetReadback sealRow exportRead ->
            PkgSig bundle exportRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row diagonal ∨ hsame row window ∨ hsame row readback ∨
                      hsame row ledger ∨ hsame row sealRow ∨ hsame row exportRead)
                  (fun row : BHist => hsame row exportRead ∧ PkgSig bundle exportRead pkg)
                  hsame ∧
                UnaryHistory budgetWindow ∧ UnaryHistory budgetReadback ∧
                  UnaryHistory exportRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle exportRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier windowLedgerBudgetWindow budgetWindowReadbackBudgetReadback
    budgetReadbackSealExport exportPkg
  obtain
    ⟨_inputUnary, _modulusUnary, diagonalUnary, windowUnary, ledgerUnary,
      _transportsUnary, _routesUnary, _provenanceUnary, _inputModulusDiagonal,
      diagonalWindowReadback, readbackLedgerSeal, _sealTransportsRoutes,
      _provenanceSealName, _sameName, provenancePkg, _namePkg⟩ :=
      carrier
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed diagonalUnary windowUnary diagonalWindowReadback
  have sealRowUnary : UnaryHistory sealRow :=
    unary_cont_closed readbackUnary ledgerUnary readbackLedgerSeal
  have budgetWindowUnary : UnaryHistory budgetWindow :=
    unary_cont_closed windowUnary ledgerUnary windowLedgerBudgetWindow
  have budgetReadbackUnary : UnaryHistory budgetReadback :=
    unary_cont_closed budgetWindowUnary readbackUnary budgetWindowReadbackBudgetReadback
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed budgetReadbackUnary sealRowUnary budgetReadbackSealExport
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row diagonal ∨ hsame row window ∨ hsame row readback ∨
              hsame row ledger ∨ hsame row sealRow ∨ hsame row exportRead)
          (fun row : BHist => hsame row exportRead ∧ PkgSig bundle exportRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro exportRead ⟨hsame_refl exportRead, exportReadUnary⟩
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
        intro _row _row' sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, exportPkg⟩
  }
  exact
    ⟨cert, budgetWindowUnary, budgetReadbackUnary, exportReadUnary, provenancePkg,
      exportPkg⟩

end BEDC.Derived.RegularCauchyLimitClassifierUp
