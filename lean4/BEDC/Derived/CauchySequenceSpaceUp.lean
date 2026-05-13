import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchySequenceSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchySequenceSpaceCarrierSurface [AskSetup] [PackageSetup]
    (F sigma W epsilon Q H C P N endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory F ∧ UnaryHistory sigma ∧ UnaryHistory W ∧ UnaryHistory epsilon ∧
    UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ UnaryHistory endpoint ∧ Cont F sigma W ∧
        Cont W epsilon Q ∧ Cont Q N endpoint ∧ PkgSig bundle endpoint pkg

theorem CauchySequenceSpaceCommonWindowClassifierTransport [AskSetup] [PackageSetup]
    {F sigma W epsilon Q H C P N endpoint F' sigma' W' epsilon' Q' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceSpaceCarrierSurface F sigma W epsilon Q H C P N endpoint bundle pkg ->
      hsame F F' ->
        hsame sigma sigma' ->
          hsame W W' ->
            hsame epsilon epsilon' ->
              Cont F' sigma' W' ->
                Cont W' epsilon' Q' ->
                  Cont Q' N endpoint' ->
                    PkgSig bundle endpoint' pkg ->
                      CauchySequenceSpaceCarrierSurface F' sigma' W' epsilon' Q' H C P N
                          endpoint' bundle pkg ∧
                        hsame Q Q' ∧ hsame endpoint endpoint' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier sameF sameSigma sameW sameEpsilon windowRoute toleranceRoute endpointRoute
    pkgSig'
  obtain ⟨fUnary, sigmaUnary, wUnary, epsilonUnary, _qUnary, hUnary, cUnary, pUnary,
    nUnary, _endpointUnary, _oldWindowRoute, oldToleranceRoute, oldEndpointRoute,
    _pkgSig⟩ := carrier
  have fUnary' : UnaryHistory F' := unary_transport fUnary sameF
  have sigmaUnary' : UnaryHistory sigma' := unary_transport sigmaUnary sameSigma
  have wUnary' : UnaryHistory W' := unary_transport wUnary sameW
  have epsilonUnary' : UnaryHistory epsilon' := unary_transport epsilonUnary sameEpsilon
  have qSame : hsame Q Q' :=
    cont_respects_hsame sameW sameEpsilon oldToleranceRoute toleranceRoute
  have qUnary' : UnaryHistory Q' :=
    unary_cont_closed wUnary' epsilonUnary' toleranceRoute
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame qSame (hsame_refl N) oldEndpointRoute endpointRoute
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed qUnary' nUnary endpointRoute
  exact
    ⟨⟨fUnary', sigmaUnary', wUnary', epsilonUnary', qUnary', hUnary, cUnary, pUnary,
      nUnary, endpointUnary', windowRoute, toleranceRoute, endpointRoute, pkgSig'⟩,
      qSame, endpointSame⟩

theorem CauchySequenceSpaceCarrier_dyadic_tolerance_ledger_exactness [AskSetup] [PackageSetup]
    {F sigma W epsilon Q H C P N endpoint toleranceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceSpaceCarrierSurface F sigma W epsilon Q H C P N endpoint bundle pkg ->
      Cont W epsilon toleranceRead ->
        UnaryHistory W ∧ UnaryHistory epsilon ∧ UnaryHistory toleranceRead ∧
          hsame Q toleranceRead ∧ Cont W epsilon toleranceRead ∧
            PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier toleranceRoute
  obtain ⟨_fUnary, _sigmaUnary, wUnary, epsilonUnary, _qUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _endpointUnary, _windowRoute, storedToleranceRoute,
    _endpointRoute, pkgSig⟩ := carrier
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed wUnary epsilonUnary toleranceRoute
  have toleranceSame : hsame Q toleranceRead :=
    cont_respects_hsame (hsame_refl W) (hsame_refl epsilon) storedToleranceRoute
      toleranceRoute
  exact
    ⟨wUnary, epsilonUnary, toleranceReadUnary, toleranceSame, toleranceRoute, pkgSig⟩

def CauchySequenceSpaceCarrier [AskSetup] [PackageSetup]
    (family schedule window tolerance completion transport route name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory family ∧ UnaryHistory schedule ∧ UnaryHistory window ∧
    UnaryHistory tolerance ∧ UnaryHistory completion ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory name ∧ Cont family schedule window ∧
        Cont window tolerance completion ∧ Cont completion transport route ∧
          PkgSig bundle route pkg ∧ PkgSig bundle name pkg

theorem CauchySequenceSpaceCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {family schedule window tolerance completion transport route name : BHist} :
    CauchySequenceSpaceCarrier family schedule window tolerance completion transport route name
        bundle pkg ->
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
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro completion (And.intro carrier (hsame_refl completion))
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem CauchySequenceSpaceCarrier_completion_handoff [AskSetup] [PackageSetup]
    {family schedule window tolerance completion transport route name handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceSpaceCarrier family schedule window tolerance completion transport route name
        bundle pkg ->
      Cont route name handoff ->
        UnaryHistory family ∧ UnaryHistory schedule ∧ UnaryHistory window ∧
          UnaryHistory tolerance ∧ UnaryHistory completion ∧ UnaryHistory route ∧
            UnaryHistory handoff ∧ Cont family schedule window ∧
              Cont window tolerance completion ∧ Cont completion transport route ∧
                Cont route name handoff ∧ PkgSig bundle route pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier routeToHandoff
  obtain ⟨familyUnary, scheduleUnary, windowUnary, toleranceUnary, completionUnary,
    _transportUnary, routeUnary, nameUnary, familyRoute, toleranceRoute, completionRoute,
    routePkg, _namePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed routeUnary nameUnary routeToHandoff
  exact
    ⟨familyUnary, scheduleUnary, windowUnary, toleranceUnary, completionUnary, routeUnary,
      handoffUnary, familyRoute, toleranceRoute, completionRoute, routeToHandoff, routePkg⟩

theorem CauchySequenceSpaceCarrier_cofinal_schedule_stability [AskSetup] [PackageSetup]
    {family schedule window tolerance completion transport route name family' schedule' window'
      completion' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceSpaceCarrier family schedule window tolerance completion transport route name
        bundle pkg ->
      hsame family family' ->
        hsame schedule schedule' ->
          Cont family' schedule' window' ->
            Cont window' tolerance completion' ->
              UnaryHistory window' ∧ UnaryHistory completion' ∧ hsame window window' ∧
                hsame completion completion' ∧ Cont family' schedule' window' ∧
                  Cont window' tolerance completion' ∧ PkgSig bundle route pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier sameFamily sameSchedule familyScheduleWindow windowToleranceCompletion
  obtain ⟨familyUnary, scheduleUnary, windowUnary, toleranceUnary, completionUnary,
    _transportUnary, _routeUnary, _nameUnary, familyScheduleWindowOld,
    windowToleranceCompletionOld, _completionRoute, routePkg, _namePkg⟩ := carrier
  have familyUnary' : UnaryHistory family' :=
    unary_transport familyUnary sameFamily
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary sameSchedule
  have windowUnary' : UnaryHistory window' :=
    unary_cont_closed familyUnary' scheduleUnary' familyScheduleWindow
  have windowSame : hsame window window' :=
    cont_respects_hsame sameFamily sameSchedule familyScheduleWindowOld familyScheduleWindow
  have completionUnary' : UnaryHistory completion' :=
    unary_cont_closed windowUnary' toleranceUnary windowToleranceCompletion
  have completionSame : hsame completion completion' :=
    cont_respects_hsame windowSame (hsame_refl tolerance) windowToleranceCompletionOld
      windowToleranceCompletion
  exact
    ⟨windowUnary', completionUnary', windowSame, completionSame, familyScheduleWindow,
      windowToleranceCompletion, routePkg⟩

theorem CauchySequenceSpaceCarrier_completion_handoff_stability [AskSetup] [PackageSetup]
    {family schedule window tolerance completion transport route name handoff family' schedule'
      window' tolerance' completion' route' handoff' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceSpaceCarrier family schedule window tolerance completion transport route name
        bundle pkg ->
      hsame family family' ->
        hsame schedule schedule' ->
          hsame window window' ->
            hsame tolerance tolerance' ->
              hsame completion completion' ->
                Cont family' schedule' window' ->
                  Cont window' tolerance' completion' ->
                    Cont completion' transport route' ->
                      Cont route name handoff ->
                        Cont route' name handoff' ->
                          PkgSig bundle route' pkg ->
                            CauchySequenceSpaceCarrier family' schedule' window' tolerance'
                                completion' transport route' name bundle pkg ∧
                              UnaryHistory handoff ∧ UnaryHistory handoff' ∧
                                hsame route route' ∧ hsame handoff handoff' ∧
                                  PkgSig bundle route' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier sameFamily sameSchedule sameWindow sameTolerance sameCompletion familyRoute'
    toleranceRoute' completionRoute' handoffRoute handoffRoute' routePkg'
  obtain ⟨familyUnary, scheduleUnary, windowUnary, toleranceUnary, completionUnary,
    transportUnary, routeUnary, nameUnary, _familyRoute, _toleranceRoute, completionRoute,
    _routePkg, namePkg⟩ := carrier
  have familyUnary' : UnaryHistory family' :=
    unary_transport familyUnary sameFamily
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary sameSchedule
  have windowUnary' : UnaryHistory window' :=
    unary_transport windowUnary sameWindow
  have toleranceUnary' : UnaryHistory tolerance' :=
    unary_transport toleranceUnary sameTolerance
  have completionUnary' : UnaryHistory completion' :=
    unary_transport completionUnary sameCompletion
  have routeSame : hsame route route' :=
    cont_respects_hsame sameCompletion (hsame_refl transport) completionRoute completionRoute'
  have routeUnary' : UnaryHistory route' :=
    unary_cont_closed completionUnary' transportUnary completionRoute'
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed routeUnary nameUnary handoffRoute
  have handoffUnary' : UnaryHistory handoff' :=
    unary_cont_closed routeUnary' nameUnary handoffRoute'
  have handoffSame : hsame handoff handoff' :=
    cont_respects_hsame routeSame (hsame_refl name) handoffRoute handoffRoute'
  exact
    ⟨⟨familyUnary', scheduleUnary', windowUnary', toleranceUnary', completionUnary',
        transportUnary, routeUnary', nameUnary, familyRoute', toleranceRoute',
        completionRoute', routePkg', namePkg⟩,
      handoffUnary, handoffUnary', routeSame, handoffSame, routePkg'⟩

theorem CauchySequenceSpaceCarrier_diagonal_rate_compatibility [AskSetup] [PackageSetup]
    {family schedule window tolerance completion transport route name family' schedule'
      window' tolerance' completion' transport' route' name' diagonal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
      CauchySequenceSpaceCarrier family schedule window tolerance completion transport route name
        bundle pkg ->
      CauchySequenceSpaceCarrier family' schedule' window' tolerance' completion'
          transport' route' name' bundle pkg ->
        hsame schedule schedule' ->
          hsame window window' ->
            hsame tolerance tolerance' ->
              hsame transport transport' ->
                Cont completion completion' diagonal ->
                  UnaryHistory diagonal /\ hsame completion completion' /\
                    hsame route route' /\ Cont completion completion' diagonal /\
                      PkgSig bundle route pkg /\ PkgSig bundle route' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier carrier' _sameSchedule sameWindow sameTolerance sameTransport diagonalRoute
  obtain ⟨_familyUnary, _scheduleUnary, _windowUnary, _toleranceUnary, completionUnary,
    _transportUnary, _routeUnary, _nameUnary, _familyRoute, toleranceRoute,
    completionRoute, routePkg, _namePkg⟩ := carrier
  obtain ⟨_familyUnary', _scheduleUnary', _windowUnary', _toleranceUnary',
    completionUnary', _transportUnary', _routeUnary', _nameUnary', _familyRoute',
    toleranceRoute', completionRoute', routePkg', _namePkg'⟩ := carrier'
  have sameCompletion : hsame completion completion' :=
    cont_respects_hsame sameWindow sameTolerance toleranceRoute toleranceRoute'
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameCompletion sameTransport completionRoute completionRoute'
  have diagonalUnary : UnaryHistory diagonal :=
    unary_cont_closed completionUnary completionUnary' diagonalRoute
  exact
    ⟨diagonalUnary, sameCompletion, sameRoute, diagonalRoute, routePkg, routePkg'⟩

theorem CauchySequenceSpaceCarrier_regular_family_exhaustion [AskSetup] [PackageSetup]
    {family schedule window tolerance completion transport route name handoff «seal» : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceSpaceCarrier family schedule window tolerance completion transport route name
        bundle pkg ->
      Cont route name handoff ->
        Cont handoff completion «seal» ->
          UnaryHistory family ∧ UnaryHistory schedule ∧ UnaryHistory window ∧
            UnaryHistory tolerance ∧ UnaryHistory completion ∧ UnaryHistory handoff ∧
              UnaryHistory «seal» ∧ Cont family schedule window ∧
                Cont window tolerance completion ∧ Cont completion transport route ∧
                  Cont route name handoff ∧ Cont handoff completion «seal» ∧
                    PkgSig bundle route pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier routeToHandoff handoffToSeal
  obtain ⟨familyUnary, scheduleUnary, windowUnary, toleranceUnary, completionUnary,
    _transportUnary, routeUnary, nameUnary, familyRoute, toleranceRoute, completionRoute,
    routePkg, _namePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed routeUnary nameUnary routeToHandoff
  have sealUnary : UnaryHistory «seal» :=
    unary_cont_closed handoffUnary completionUnary handoffToSeal
  exact
    ⟨familyUnary, scheduleUnary, windowUnary, toleranceUnary, completionUnary, handoffUnary,
      sealUnary, familyRoute, toleranceRoute, completionRoute, routeToHandoff, handoffToSeal,
      routePkg⟩

theorem CauchySequenceSpaceCarrier_limit_seal_factorization [AskSetup] [PackageSetup]
    {family schedule window tolerance completion transport route name handoff «seal» : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceSpaceCarrier family schedule window tolerance completion transport route name
        bundle pkg ->
      Cont route name handoff ->
        Cont handoff completion «seal» ->
          SemanticNameCert
              (fun row : BHist =>
                CauchySequenceSpaceCarrier family schedule window tolerance completion transport
                  route name bundle pkg ∧ hsame row completion)
              (fun row : BHist =>
                CauchySequenceSpaceCarrier family schedule window tolerance completion transport
                  route name bundle pkg ∧ hsame row completion)
              (fun row : BHist =>
                CauchySequenceSpaceCarrier family schedule window tolerance completion transport
                  route name bundle pkg ∧ hsame row completion)
              hsame ∧
            UnaryHistory handoff ∧ UnaryHistory «seal» ∧ Cont route name handoff ∧
              Cont handoff completion «seal» ∧ PkgSig bundle route pkg ∧
                PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier routeToHandoff handoffToSeal
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
    _transportUnary, routeUnary, nameUnary, _familyRoute, _toleranceRoute, _completionRoute,
    routePkg, namePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed routeUnary nameUnary routeToHandoff
  have sealUnary : UnaryHistory «seal» :=
    unary_cont_closed handoffUnary completionUnary handoffToSeal
  exact
    ⟨cert, handoffUnary, sealUnary, routeToHandoff, handoffToSeal, routePkg, namePkg⟩

theorem CauchySequenceSpaceCarrier_scoped_completion_route_inventory [AskSetup]
    [PackageSetup]
    {family schedule window tolerance completion transport route name handoff «seal»
      inventory : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceSpaceCarrier family schedule window tolerance completion transport route name
        bundle pkg ->
      Cont route name handoff ->
        Cont handoff completion «seal» ->
          Cont «seal» route inventory ->
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
              UnaryHistory inventory ∧ Cont «seal» route inventory ∧
                PkgSig bundle route pkg ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier routeToHandoff handoffToSeal sealToInventory
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
    _transportUnary, routeUnary, nameUnary, _familyRoute, _toleranceRoute, _completionRoute,
    routePkg, namePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed routeUnary nameUnary routeToHandoff
  have sealUnary : UnaryHistory «seal» :=
    unary_cont_closed handoffUnary completionUnary handoffToSeal
  have inventoryUnary : UnaryHistory inventory :=
    unary_cont_closed sealUnary routeUnary sealToInventory
  exact ⟨cert, inventoryUnary, sealToInventory, routePkg, namePkg⟩

theorem CauchySequenceSpaceCarrier_public_completion_export [AskSetup] [PackageSetup]
    {family schedule window tolerance completion transport route name handoff «seal»
      inventory : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceSpaceCarrier family schedule window tolerance completion transport route name
        bundle pkg ->
      Cont route name handoff ->
        Cont handoff completion «seal» ->
          Cont «seal» route inventory ->
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
                Cont route name handoff ∧ Cont handoff completion «seal» ∧
                  Cont «seal» route inventory ∧ PkgSig bundle route pkg ∧
                    PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier routeToHandoff handoffToSeal sealToInventory
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
    _transportUnary, routeUnary, nameUnary, _familyRoute, _toleranceRoute, _completionRoute,
    routePkg, namePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed routeUnary nameUnary routeToHandoff
  have sealUnary : UnaryHistory «seal» :=
    unary_cont_closed handoffUnary completionUnary handoffToSeal
  have inventoryUnary : UnaryHistory inventory :=
    unary_cont_closed sealUnary routeUnary sealToInventory
  exact
    ⟨cert, handoffUnary, sealUnary, inventoryUnary, routeToHandoff, handoffToSeal,
      sealToInventory, routePkg, namePkg⟩

end BEDC.Derived.CauchySequenceSpaceUp
