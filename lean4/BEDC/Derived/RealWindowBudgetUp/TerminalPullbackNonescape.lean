import BEDC.Derived.RealWindowBudgetUp.TerminalPullbackCoherence

namespace BEDC.Derived.RealWindowBudgetUp.TerminalPullbackNonescape

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RealWindowBudgetUp

theorem RealWindowBudgetCarrier_terminal_pullback_nonescape [AskSetup] [PackageSetup]
    {request windows dyadic handoff realSeal selector disclosure transport route provenance
      nameRow endpoint selectorTerminal exactBoundary pullback commonConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealWindowBudgetCarrier request windows dyadic handoff realSeal selector disclosure transport
        route provenance nameRow bundle pkg →
      Cont handoff realSeal endpoint →
        Cont endpoint selector selectorTerminal →
          Cont endpoint disclosure exactBoundary →
            Cont selectorTerminal exactBoundary pullback →
              Cont pullback nameRow commonConsumer →
                PkgSig bundle commonConsumer pkg →
                  SemanticNameCert
                    (fun row : BHist =>
                      RealWindowBudgetCarrier request windows dyadic handoff realSeal selector
                          disclosure transport route provenance nameRow bundle pkg ∧
                        (hsame row pullback ∨ hsame row commonConsumer))
                    (fun row : BHist =>
                      Cont selectorTerminal exactBoundary pullback ∧
                        Cont pullback nameRow commonConsumer ∧
                          (hsame row pullback ∨ hsame row commonConsumer))
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle commonConsumer pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier handoffEndpoint endpointSelectorTerminal endpointExactBoundary
    terminalBoundaryPullback pullbackNameCommon commonConsumerPkg
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed carrier.handoff_unary carrier.realSeal_unary handoffEndpoint
  have selectorTerminalUnary : UnaryHistory selectorTerminal :=
    unary_cont_closed endpointUnary carrier.selector_unary endpointSelectorTerminal
  have exactBoundaryUnary : UnaryHistory exactBoundary :=
    unary_cont_closed endpointUnary carrier.disclosure_unary endpointExactBoundary
  have pullbackUnary : UnaryHistory pullback :=
    unary_cont_closed selectorTerminalUnary exactBoundaryUnary terminalBoundaryPullback
  have commonConsumerUnary : UnaryHistory commonConsumer :=
    unary_cont_closed pullbackUnary carrier.nameRow_unary pullbackNameCommon
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro pullback ⟨carrier, Or.inl (hsame_refl pullback)⟩
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
        | inl rowPullback =>
            exact Or.inl (hsame_trans (hsame_symm same) rowPullback)
        | inr rowCommon =>
            exact Or.inr (hsame_trans (hsame_symm same) rowCommon)
    }
    pattern_sound := by
      intro _row source
      exact ⟨terminalBoundaryPullback, pullbackNameCommon, source.right⟩
    ledger_sound := by
      intro _row source
      cases source.right with
      | inl rowPullback =>
          exact
            ⟨unary_transport pullbackUnary (hsame_symm rowPullback),
              carrier.provenance_pkg, commonConsumerPkg⟩
      | inr rowCommon =>
          exact
            ⟨unary_transport commonConsumerUnary (hsame_symm rowCommon),
              carrier.provenance_pkg, commonConsumerPkg⟩
  }

end BEDC.Derived.RealWindowBudgetUp.TerminalPullbackNonescape
