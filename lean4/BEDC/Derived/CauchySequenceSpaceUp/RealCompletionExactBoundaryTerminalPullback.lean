import BEDC.Derived.CauchySequenceSpaceUp.WindowFactorization

namespace BEDC.Derived.CauchySequenceSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchySequenceSpaceCarrier_real_completion_exact_boundary_terminal_pullback
    [AskSetup] [PackageSetup]
    {family schedule window tolerance completion transport route name handoff sealRow inventory
      pullbackRead boundaryTerminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceSpaceCarrier family schedule window tolerance completion transport route name
        bundle pkg ->
      Cont route name handoff ->
        Cont handoff completion sealRow ->
          Cont sealRow route inventory ->
            Cont inventory tolerance pullbackRead ->
              PkgSig bundle boundaryTerminalRead pkg ->
                hsame pullbackRead boundaryTerminalRead ->
                  SemanticNameCert
                      (fun row : BHist =>
                        CauchySequenceSpaceCarrier family schedule window tolerance completion
                          transport route name bundle pkg ∧ hsame row completion)
                      (fun row : BHist =>
                        CauchySequenceSpaceCarrier family schedule window tolerance completion
                          transport route name bundle pkg ∧ hsame row completion)
                      (fun row : BHist =>
                        CauchySequenceSpaceCarrier family schedule window tolerance completion
                          transport route name bundle pkg ∧ hsame row completion)
                      hsame ∧
                    UnaryHistory pullbackRead ∧ hsame pullbackRead boundaryTerminalRead ∧
                      Cont inventory tolerance pullbackRead ∧
                        PkgSig bundle boundaryTerminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert UnaryHistory
  intro carrier routeToHandoff handoffToSeal sealToInventory inventoryToPullback
    boundaryPkg sameBoundary
  have tailFacts :
      SemanticNameCert
          (fun row : BHist =>
            CauchySequenceSpaceCarrier family schedule window tolerance completion transport route
              name bundle pkg ∧ hsame row completion)
          (fun row : BHist =>
            CauchySequenceSpaceCarrier family schedule window tolerance completion transport route
              name bundle pkg ∧ hsame row completion)
          (fun row : BHist =>
            CauchySequenceSpaceCarrier family schedule window tolerance completion transport route
              name bundle pkg ∧ hsame row completion)
          hsame ∧
        UnaryHistory handoff ∧ UnaryHistory sealRow ∧ UnaryHistory inventory ∧
          UnaryHistory pullbackRead ∧ Cont route name handoff ∧
            Cont handoff completion sealRow ∧ Cont sealRow route inventory ∧
              Cont inventory tolerance pullbackRead ∧ PkgSig bundle route pkg ∧
                PkgSig bundle name pkg :=
    CauchySequenceSpaceCarrier_tail_window_factorization carrier routeToHandoff handoffToSeal
      sealToInventory inventoryToPullback
  obtain ⟨cert, _handoffUnary, _sealUnary, _inventoryUnary, pullbackUnary,
    _routeToHandoff, _handoffToSeal, _sealToInventory, inventoryToPullbackRow,
    _routePkg, _namePkg⟩ := tailFacts
  exact ⟨cert, pullbackUnary, sameBoundary, inventoryToPullbackRow, boundaryPkg⟩

end BEDC.Derived.CauchySequenceSpaceUp
