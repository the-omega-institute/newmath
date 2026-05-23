import BEDC.Derived.CauchySequenceSpaceUp

namespace BEDC.Derived.CauchySequenceSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchySequenceSpaceUp_StdBridge [AskSetup] [PackageSetup]
    {family schedule window tolerance completion transport route name handoff sealRow
      inventory : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceSpaceCarrier family schedule window tolerance completion transport route name
        bundle pkg ->
      Cont route name handoff ->
        Cont handoff completion sealRow ->
          Cont sealRow route inventory ->
            SemanticNameCert
                (fun row : BHist =>
                  CauchySequenceSpaceCarrier family schedule window tolerance completion
                      transport route name bundle pkg ∧
                    hsame row completion ∧ Cont sealRow route inventory)
                (fun row : BHist =>
                  CauchySequenceSpaceCarrier family schedule window tolerance completion
                      transport route name bundle pkg ∧
                    hsame row completion)
                (fun row : BHist =>
                  CauchySequenceSpaceCarrier family schedule window tolerance completion
                      transport route name bundle pkg ∧
                    hsame row completion ∧ Cont sealRow route inventory)
                hsame ∧
              UnaryHistory handoff ∧ UnaryHistory sealRow ∧ UnaryHistory inventory ∧
                Cont route name handoff ∧ Cont handoff completion sealRow ∧
                  Cont sealRow route inventory ∧ PkgSig bundle route pkg ∧
                    PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier routeToHandoff handoffToSeal sealToInventory
  have carrierPacket :
      CauchySequenceSpaceCarrier family schedule window tolerance completion transport route name
        bundle pkg :=
    carrier
  obtain ⟨_familyUnary, _scheduleUnary, _windowUnary, _toleranceUnary, completionUnary,
    _transportUnary, routeUnary, nameUnary, _familyRoute, _completionRoute, _transportRoute,
    routePkg, namePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed routeUnary nameUnary routeToHandoff
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed handoffUnary completionUnary handoffToSeal
  have inventoryUnary : UnaryHistory inventory :=
    unary_cont_closed sealUnary routeUnary sealToInventory
  have sourceAtCompletion :
    CauchySequenceSpaceCarrier family schedule window tolerance completion transport route name
          bundle pkg ∧
        hsame completion completion ∧ Cont sealRow route inventory :=
    ⟨carrierPacket, hsame_refl completion, sealToInventory⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            CauchySequenceSpaceCarrier family schedule window tolerance completion transport route
                name bundle pkg ∧
              hsame row completion ∧ Cont sealRow route inventory)
          (fun row : BHist =>
            CauchySequenceSpaceCarrier family schedule window tolerance completion transport route
                name bundle pkg ∧
              hsame row completion)
          (fun row : BHist =>
            CauchySequenceSpaceCarrier family schedule window tolerance completion transport route
                name bundle pkg ∧
              hsame row completion ∧ Cont sealRow route inventory)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completion sourceAtCompletion
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
        intro _row _row' sameRows source
        exact
          ⟨source.left,
            hsame_trans (hsame_symm sameRows) source.right.left,
            source.right.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, source.right.left⟩
    ledger_sound := by
      intro _row source
      exact source
  }
  exact
    ⟨cert, handoffUnary, sealUnary, inventoryUnary, routeToHandoff, handoffToSeal,
      sealToInventory, routePkg, namePkg⟩

end BEDC.Derived.CauchySequenceSpaceUp
