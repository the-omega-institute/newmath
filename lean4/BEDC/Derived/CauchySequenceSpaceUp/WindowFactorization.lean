import BEDC.Derived.CauchySequenceSpaceUp

namespace BEDC.Derived.CauchySequenceSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchySequenceSpaceCarrier_regular_window_factorization [AskSetup] [PackageSetup]
    {family schedule window tolerance completion transport route name windowRead completionRead
      routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceSpaceCarrier family schedule window tolerance completion transport route name
        bundle pkg →
      Cont family schedule windowRead →
        Cont windowRead tolerance completionRead →
          Cont completionRead transport routeRead →
            PkgSig bundle routeRead pkg →
              CauchySequenceSpaceCarrier family schedule windowRead tolerance completionRead
                  transport routeRead name bundle pkg ∧
                hsame window windowRead ∧ hsame completion completionRead ∧
                  hsame route routeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier familyScheduleRead windowToleranceRead completionTransportRead routeReadPkg
  obtain ⟨familyUnary, scheduleUnary, _windowUnary, toleranceUnary, _completionUnary,
    transportUnary, _routeUnary, nameUnary, familyScheduleWindow, windowToleranceCompletion,
    completionTransportRoute, _routePkg, namePkg⟩ := carrier
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed familyUnary scheduleUnary familyScheduleRead
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed windowReadUnary toleranceUnary windowToleranceRead
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed completionReadUnary transportUnary completionTransportRead
  have sameWindow : hsame window windowRead :=
    cont_respects_hsame (hsame_refl family) (hsame_refl schedule) familyScheduleWindow
      familyScheduleRead
  have sameCompletion : hsame completion completionRead :=
    cont_respects_hsame sameWindow (hsame_refl tolerance) windowToleranceCompletion
      windowToleranceRead
  have sameRoute : hsame route routeRead :=
    cont_respects_hsame sameCompletion (hsame_refl transport) completionTransportRoute
      completionTransportRead
  exact
    ⟨⟨familyUnary, scheduleUnary, windowReadUnary, toleranceUnary, completionReadUnary,
        transportUnary, routeReadUnary, nameUnary, familyScheduleRead, windowToleranceRead,
        completionTransportRead, routeReadPkg, namePkg⟩,
      sameWindow, sameCompletion, sameRoute⟩

theorem CauchySequenceSpaceCarrier_tail_window_factorization [AskSetup] [PackageSetup]
    {family schedule window tolerance completion transport route name handoff «seal» inventory
      tail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceSpaceCarrier family schedule window tolerance completion transport route name
        bundle pkg →
      Cont route name handoff →
        Cont handoff completion «seal» →
          Cont «seal» route inventory →
            Cont inventory tolerance tail →
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
                UnaryHistory handoff ∧ UnaryHistory «seal» ∧ UnaryHistory inventory ∧
                  UnaryHistory tail ∧ Cont route name handoff ∧
                    Cont handoff completion «seal» ∧ Cont «seal» route inventory ∧
                      Cont inventory tolerance tail ∧ PkgSig bundle route pkg ∧
                        PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert UnaryHistory
  intro carrier routeToHandoff handoffToSeal sealToInventory inventoryToTail
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
  obtain ⟨_familyUnary, _scheduleUnary, _windowUnary, toleranceUnary, completionUnary,
    _transportUnary, routeUnary, nameUnary, _familyRoute, _toleranceRoute, _completionRoute,
    routePkg, namePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed routeUnary nameUnary routeToHandoff
  have sealUnary : UnaryHistory «seal» :=
    unary_cont_closed handoffUnary completionUnary handoffToSeal
  have inventoryUnary : UnaryHistory inventory :=
    unary_cont_closed sealUnary routeUnary sealToInventory
  have tailUnary : UnaryHistory tail :=
    unary_cont_closed inventoryUnary toleranceUnary inventoryToTail
  exact
    ⟨cert, handoffUnary, sealUnary, inventoryUnary, tailUnary, routeToHandoff, handoffToSeal,
      sealToInventory, inventoryToTail, routePkg, namePkg⟩

end BEDC.Derived.CauchySequenceSpaceUp
