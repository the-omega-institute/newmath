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

theorem RegularCauchyLimitClassifierCarrier_synchronizer_factorization
    [AskSetup] [PackageSetup]
    {input modulus diagonal windows readback ledger sealRow transportRow routes provenance cert
      syncBudget syncThreshold syncSeal syncRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitClassifierCarrier input modulus diagonal windows readback ledger sealRow
      transportRow routes provenance cert bundle pkg ->
    Cont windows ledger syncBudget ->
    Cont syncBudget readback syncThreshold ->
    Cont syncThreshold sealRow syncSeal ->
    Cont syncSeal routes syncRead ->
    PkgSig bundle syncRead pkg ->
      SemanticNameCert
        (fun row : BHist => hsame row syncRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row windows ∨ hsame row readback ∨ hsame row ledger ∨
            hsame row sealRow ∨ hsame row syncRead)
        (fun row : BHist => hsame row syncRead ∧ PkgSig bundle syncRead pkg)
        hsame ∧ UnaryHistory syncBudget ∧ UnaryHistory syncThreshold ∧
          UnaryHistory syncSeal ∧ UnaryHistory syncRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier windowsLedgerSyncBudget syncBudgetReadbackSyncThreshold
    syncThresholdSealSyncSeal syncSealRoutesSyncRead syncReadPkg
  obtain ⟨_inputUnary, _modulusUnary, diagonalUnary, windowsUnary, ledgerUnary,
    _transportUnary, routesUnary, _provenanceUnary, _inputModulusDiagonal,
    diagonalWindowsReadback, readbackLedgerSeal, _sealTransportRoutes, _provenanceSealCert,
    _sameCert, _provenancePkg, _certPkg⟩ := carrier
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsReadback
  have sealRowUnary : UnaryHistory sealRow :=
    unary_cont_closed readbackUnary ledgerUnary readbackLedgerSeal
  have syncBudgetUnary : UnaryHistory syncBudget :=
    unary_cont_closed windowsUnary ledgerUnary windowsLedgerSyncBudget
  have syncThresholdUnary : UnaryHistory syncThreshold :=
    unary_cont_closed syncBudgetUnary readbackUnary syncBudgetReadbackSyncThreshold
  have syncSealUnary : UnaryHistory syncSeal :=
    unary_cont_closed syncThresholdUnary sealRowUnary syncThresholdSealSyncSeal
  have syncReadUnary : UnaryHistory syncRead :=
    unary_cont_closed syncSealUnary routesUnary syncSealRoutesSyncRead
  have certRoute :
      SemanticNameCert
        (fun row : BHist => hsame row syncRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row windows ∨ hsame row readback ∨ hsame row ledger ∨
            hsame row sealRow ∨ hsame row syncRead)
        (fun row : BHist => hsame row syncRead ∧ PkgSig bundle syncRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro syncRead
        ⟨hsame_refl syncRead, syncReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, syncReadPkg⟩
  }
  exact
    ⟨certRoute, syncBudgetUnary, syncThresholdUnary, syncSealUnary, syncReadUnary⟩

end BEDC.Derived.RegularCauchyLimitClassifierUp
