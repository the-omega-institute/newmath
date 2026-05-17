import BEDC.Derived.RealWindowBudgetUp

namespace BEDC.Derived.RealWindowBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealWindowBudgetCarrier_terminal_pullback_coherence [AskSetup] [PackageSetup]
    {request windows dyadic handoff realSeal selector disclosure transport route provenance
      nameRow endpoint selectorTerminal exactBoundary pullback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealWindowBudgetCarrier request windows dyadic handoff realSeal selector disclosure transport
        route provenance nameRow bundle pkg →
      Cont handoff realSeal endpoint →
        Cont endpoint selector selectorTerminal →
          Cont endpoint disclosure exactBoundary →
            Cont selectorTerminal exactBoundary pullback →
              PkgSig bundle endpoint pkg →
                PkgSig bundle selectorTerminal pkg →
                  PkgSig bundle exactBoundary pkg →
                    PkgSig bundle pullback pkg →
                      SemanticNameCert
                        (fun row : BHist =>
                          RealWindowBudgetCarrier request windows dyadic handoff realSeal selector
                              disclosure transport route provenance nameRow bundle pkg ∧
                            (hsame row endpoint ∨ hsame row selectorTerminal ∨
                              hsame row exactBoundary ∨ hsame row pullback))
                        (fun row : BHist =>
                          Cont handoff realSeal endpoint ∧
                            Cont endpoint selector selectorTerminal ∧
                              Cont endpoint disclosure exactBoundary ∧
                                Cont selectorTerminal exactBoundary pullback ∧
                                  (hsame row endpoint ∨ hsame row selectorTerminal ∨
                                    hsame row exactBoundary ∨ hsame row pullback))
                        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier handoffEndpoint endpointSelectorTerminal endpointExactBoundary
    terminalBoundaryPullback _endpointPkg _selectorTerminalPkg _exactBoundaryPkg _pullbackPkg
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed carrier.handoff_unary carrier.realSeal_unary handoffEndpoint
  have selectorTerminalUnary : UnaryHistory selectorTerminal :=
    unary_cont_closed endpointUnary carrier.selector_unary endpointSelectorTerminal
  have exactBoundaryUnary : UnaryHistory exactBoundary :=
    unary_cont_closed endpointUnary carrier.disclosure_unary endpointExactBoundary
  have pullbackUnary : UnaryHistory pullback :=
    unary_cont_closed selectorTerminalUnary exactBoundaryUnary terminalBoundaryPullback
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint ⟨carrier, Or.inl (hsame_refl endpoint)⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same source
        refine ⟨source.left, ?_⟩
        cases source.right with
        | inl rowEndpoint =>
            exact Or.inl (hsame_trans (hsame_symm same) rowEndpoint)
        | inr tail =>
            cases tail with
            | inl rowSelectorTerminal =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm same) rowSelectorTerminal))
            | inr tail' =>
                cases tail' with
                | inl rowExactBoundary =>
                    exact Or.inr
                      (Or.inr (Or.inl (hsame_trans (hsame_symm same) rowExactBoundary)))
                | inr rowPullback =>
                    exact Or.inr
                      (Or.inr (Or.inr (hsame_trans (hsame_symm same) rowPullback)))
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨handoffEndpoint, endpointSelectorTerminal, endpointExactBoundary,
          terminalBoundaryPullback, source.right⟩
    ledger_sound := by
      intro _row source
      cases source.right with
      | inl rowEndpoint =>
          exact
            ⟨unary_transport endpointUnary (hsame_symm rowEndpoint), carrier.provenance_pkg⟩
      | inr tail =>
          cases tail with
          | inl rowSelectorTerminal =>
              exact
                ⟨unary_transport selectorTerminalUnary (hsame_symm rowSelectorTerminal),
                  carrier.provenance_pkg⟩
          | inr tail' =>
              cases tail' with
              | inl rowExactBoundary =>
                  exact
                    ⟨unary_transport exactBoundaryUnary (hsame_symm rowExactBoundary),
                      carrier.provenance_pkg⟩
              | inr rowPullback =>
                  exact
                    ⟨unary_transport pullbackUnary (hsame_symm rowPullback),
                      carrier.provenance_pkg⟩
  }

end BEDC.Derived.RealWindowBudgetUp
