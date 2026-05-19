import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_ledger_nonescape [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name refusal
      ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont terminal normal refusal →
        Cont refusal continuation ledgerRead →
          PkgSig bundle ledgerRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row terminal ∨ hsame row normal ∨ hsame row refusal ∨
                    hsame row continuation ∨ hsame row ledgerRead)
                (fun row : BHist => hsame row ledgerRead ∧ PkgSig bundle ledgerRead pkg)
                hsame ∧
              UnaryHistory refusal ∧ UnaryHistory ledgerRead ∧
                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet terminalNormalRefusal refusalContinuationLedgerRead ledgerReadPkg
  obtain ⟨_typedUnary, _fuelUnary, terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have refusalUnary : UnaryHistory refusal :=
    unary_cont_closed terminalUnary normalUnary terminalNormalRefusal
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed refusalUnary continuationUnary refusalContinuationLedgerRead
  have ledgerReadSource :
      (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row) ledgerRead := by
    exact ⟨hsame_refl ledgerRead, ledgerReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row terminal ∨ hsame row normal ∨ hsame row refusal ∨
              hsame row continuation ∨ hsame row ledgerRead)
          (fun row : BHist => hsame row ledgerRead ∧ PkgSig bundle ledgerRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro ledgerRead ledgerReadSource
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
      exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, ledgerReadPkg⟩
  }
  exact ⟨cert, refusalUnary, ledgerReadUnary, provenancePkg⟩

end BEDC.Derived.ZnormalUp
