import BEDC.Derived.ContextFreeGrammarUp

namespace BEDC.Derived.ContextFreeGrammarUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContextFreeGrammarPushdownHandoff [AskSetup] [PackageSetup]
    {terminal nonterminal start production yield derivation readback transport route provenance name
      endpoint stackRun handoffEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContextFreeGrammarPacket terminal nonterminal start production yield derivation readback
        transport route provenance name endpoint bundle pkg ->
      Cont start production stackRun ->
        Cont stackRun readback handoffEndpoint ->
          PkgSig bundle handoffEndpoint pkg ->
            SemanticNameCert
              (fun row : BHist => hsame row handoffEndpoint ∧ UnaryHistory row ∧
                PkgSig bundle row pkg)
              (fun row : BHist =>
                hsame row start ∨ hsame row production ∨ hsame row derivation ∨
                  hsame row readback ∨ hsame row stackRun ∨ hsame row handoffEndpoint ∨
                    hsame row endpoint)
              (fun row : BHist =>
                hsame row handoffEndpoint ∧ Cont start production stackRun ∧
                  Cont stackRun readback handoffEndpoint ∧ PkgSig bundle endpoint pkg)
              hsame ∧ UnaryHistory stackRun ∧ UnaryHistory handoffEndpoint := by
  -- BEDC touchpoint anchor: ContextFreeGrammarPacket BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro packet startProductionStack stackReadbackHandoff handoffPkg
  obtain ⟨_terminalUnary, _nonterminalUnary, startUnary, productionUnary, _yieldUnary,
    _derivationUnary, readbackUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _nameUnary, _endpointUnary, _terminalNonterminalStart, _productionYieldReadback,
    _derivationTransportRoute, _routeProvenanceName, _nameEndpointEndpoint,
    endpointPkg⟩ := packet
  have stackUnary : UnaryHistory stackRun :=
    unary_cont_closed startUnary productionUnary startProductionStack
  have handoffUnary : UnaryHistory handoffEndpoint :=
    unary_cont_closed stackUnary readbackUnary stackReadbackHandoff
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row handoffEndpoint ∧ UnaryHistory row ∧
          PkgSig bundle row pkg)
        (fun row : BHist =>
          hsame row start ∨ hsame row production ∨ hsame row derivation ∨
            hsame row readback ∨ hsame row stackRun ∨ hsame row handoffEndpoint ∨
              hsame row endpoint)
        (fun row : BHist =>
          hsame row handoffEndpoint ∧ Cont start production stackRun ∧
            Cont stackRun readback handoffEndpoint ∧ PkgSig bundle endpoint pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffEndpoint
        ⟨hsame_refl handoffEndpoint, handoffUnary, handoffPkg⟩
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
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, startProductionStack, stackReadbackHandoff, endpointPkg⟩
  }
  exact ⟨cert, stackUnary, handoffUnary⟩

end BEDC.Derived.ContextFreeGrammarUp
