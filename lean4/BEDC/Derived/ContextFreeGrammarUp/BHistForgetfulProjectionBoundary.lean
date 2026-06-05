import BEDC.Derived.ContextFreeGrammarUp

namespace BEDC.Derived.ContextFreeGrammarUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContextFreeGrammarPacket_bhist_forgetful_projection_boundary [AskSetup]
    [PackageSetup]
    {terminal nonterminal start production yield derivation readback transport route provenance
      name endpoint productionRead derivationRead boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContextFreeGrammarPacket terminal nonterminal start production yield derivation readback
        transport route provenance name endpoint bundle pkg ->
      Cont production yield productionRead ->
        Cont derivation readback derivationRead ->
          Cont name endpoint boundary ->
            PkgSig bundle boundary pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row boundary ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                  (fun row : BHist =>
                    hsame row terminal ∨ hsame row nonterminal ∨ hsame row start ∨
                      hsame row production ∨ hsame row yield ∨ hsame row derivation ∨
                        hsame row readback ∨ hsame row productionRead ∨
                          hsame row derivationRead ∨ hsame row boundary)
                  (fun row : BHist =>
                    hsame row boundary ∧ Cont production yield productionRead ∧
                      Cont derivation readback derivationRead ∧
                        Cont name endpoint boundary ∧ PkgSig bundle endpoint pkg)
                  hsame ∧ UnaryHistory productionRead ∧ UnaryHistory derivationRead ∧
                    UnaryHistory boundary := by
  -- BEDC touchpoint anchor: ContextFreeGrammarPacket BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro packet productionYieldRead derivationReadbackRead nameEndpointBoundary boundaryPkg
  obtain ⟨_terminalUnary, _nonterminalUnary, _startUnary, productionUnary, yieldUnary,
    derivationUnary, readbackUnary, _transportUnary, _routeUnary, _provenanceUnary,
    nameUnary, endpointUnary, _terminalNonterminalStart, _productionYieldReadback,
    _derivationTransportRoute, _routeProvenanceName, _nameEndpointEndpoint,
    endpointPkg⟩ := packet
  have productionReadUnary : UnaryHistory productionRead :=
    unary_cont_closed productionUnary yieldUnary productionYieldRead
  have derivationReadUnary : UnaryHistory derivationRead :=
    unary_cont_closed derivationUnary readbackUnary derivationReadbackRead
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed nameUnary endpointUnary nameEndpointBoundary
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row boundary ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row terminal ∨ hsame row nonterminal ∨ hsame row start ∨
              hsame row production ∨ hsame row yield ∨ hsame row derivation ∨
                hsame row readback ∨ hsame row productionRead ∨
                  hsame row derivationRead ∨ hsame row boundary)
          (fun row : BHist =>
            hsame row boundary ∧ Cont production yield productionRead ∧
              Cont derivation readback derivationRead ∧
                Cont name endpoint boundary ∧ PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundary
        ⟨hsame_refl boundary, boundaryUnary, boundaryPkg⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr sourceRow.left))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.left, productionYieldRead, derivationReadbackRead,
          nameEndpointBoundary, endpointPkg⟩
  }
  exact ⟨cert, productionReadUnary, derivationReadUnary, boundaryUnary⟩

end BEDC.Derived.ContextFreeGrammarUp
