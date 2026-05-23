import BEDC.Derived.CauchySequenceSpaceUp

namespace BEDC.Derived.CauchySequenceSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchySequenceSpaceCarrier_real_observation_budget_factorization [AskSetup]
    [PackageSetup]
    {family schedule window tolerance completion transport route name handoff sealRow inventory
      observation : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceSpaceCarrier family schedule window tolerance completion transport route name
        bundle pkg ->
      Cont route name handoff ->
        Cont handoff completion sealRow ->
          Cont sealRow route inventory ->
            Cont inventory completion observation ->
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
                UnaryHistory observation ∧ Cont inventory completion observation ∧
                  PkgSig bundle route pkg ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert UnaryHistory
  intro carrier routeToHandoff handoffToSeal sealToInventory inventoryToObservation
  have cert :
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
        hsame :=
    CauchySequenceSpaceCarrier_namecert_obligation_surface carrier
  obtain ⟨_familyUnary, _scheduleUnary, _windowUnary, _toleranceUnary, completionUnary,
    _transportUnary, routeUnary, nameUnary, _familyRoute, _windowToleranceCompletion,
    _completionTransportRoute, routePkg, namePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed routeUnary nameUnary routeToHandoff
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed handoffUnary completionUnary handoffToSeal
  have inventoryUnary : UnaryHistory inventory :=
    unary_cont_closed sealUnary routeUnary sealToInventory
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed inventoryUnary completionUnary inventoryToObservation
  exact ⟨cert, observationUnary, inventoryToObservation, routePkg, namePkg⟩

end BEDC.Derived.CauchySequenceSpaceUp
