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

theorem RegularCauchyLimitClassifierCarrier_budget_synchronizer_route_agreement
    [AskSetup] [PackageSetup]
    {input modulus diagonal windows readback ledger sealRow transportRow routes provenance cert
      budgetWindow budgetReadback exportRead synchronizerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitClassifierCarrier input modulus diagonal windows readback ledger sealRow
        transportRow routes provenance cert bundle pkg →
      Cont windows ledger budgetWindow →
        Cont budgetWindow readback budgetReadback →
          Cont budgetReadback sealRow exportRead →
            Cont exportRead transportRow synchronizerRead →
              PkgSig bundle synchronizerRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row synchronizerRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row windows ∨ hsame row readback ∨ hsame row ledger ∨
                        hsame row sealRow ∨ hsame row exportRead ∨
                          hsame row synchronizerRead)
                    (fun row : BHist =>
                      hsame row synchronizerRead ∧ PkgSig bundle synchronizerRead pkg)
                    hsame ∧
                  UnaryHistory budgetWindow ∧ UnaryHistory budgetReadback ∧
                    UnaryHistory exportRead ∧ UnaryHistory synchronizerRead ∧
                      PkgSig bundle provenance pkg ∧
                        PkgSig bundle synchronizerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier windowsLedgerBudget budgetWindowReadbackBudget
    budgetReadbackSealExport exportTransportSynchronizer synchronizerPkg
  obtain
    ⟨_inputUnary, _modulusUnary, diagonalUnary, windowsUnary, ledgerUnary,
      transportUnary, _routesUnary, _provenanceUnary, _inputModulusDiagonal,
      diagonalWindowsReadback, readbackLedgerSeal, _sealTransportRoutes,
      _provenanceSealCert, _sameCert, provenancePkg, _certPkg⟩ := carrier
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsReadback
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed readbackUnary ledgerUnary readbackLedgerSeal
  have budgetWindowUnary : UnaryHistory budgetWindow :=
    unary_cont_closed windowsUnary ledgerUnary windowsLedgerBudget
  have budgetReadbackUnary : UnaryHistory budgetReadback :=
    unary_cont_closed budgetWindowUnary readbackUnary budgetWindowReadbackBudget
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed budgetReadbackUnary sealUnary budgetReadbackSealExport
  have synchronizerUnary : UnaryHistory synchronizerRead :=
    unary_cont_closed exportReadUnary transportUnary exportTransportSynchronizer
  have sourceSynchronizer :
      (fun row : BHist => hsame row synchronizerRead ∧ UnaryHistory row)
        synchronizerRead := by
    exact ⟨hsame_refl synchronizerRead, synchronizerUnary⟩
  have certRoute :
      SemanticNameCert
        (fun row : BHist => hsame row synchronizerRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row windows ∨ hsame row readback ∨ hsame row ledger ∨
            hsame row sealRow ∨ hsame row exportRead ∨ hsame row synchronizerRead)
        (fun row : BHist =>
          hsame row synchronizerRead ∧ PkgSig bundle synchronizerRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro synchronizerRead sourceSynchronizer
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
      exact ⟨sourceRow.left, synchronizerPkg⟩
  }
  exact
    ⟨certRoute, budgetWindowUnary, budgetReadbackUnary, exportReadUnary,
      synchronizerUnary, provenancePkg, synchronizerPkg⟩

end BEDC.Derived.RegularCauchyLimitClassifierUp
