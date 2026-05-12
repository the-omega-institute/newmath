import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyCompletionMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyCompletionMonadPacket [AskSetup] [PackageSetup]
    (sourceFamily windows observations schedule diagonal sealRow transport route nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sourceFamily ∧ UnaryHistory windows ∧ UnaryHistory schedule ∧
    UnaryHistory diagonal ∧ UnaryHistory transport ∧ UnaryHistory nameRow ∧
      Cont schedule windows observations ∧ Cont observations diagonal sealRow ∧
        Cont sealRow transport route ∧ Cont route nameRow sealRow ∧
          PkgSig bundle sealRow pkg

theorem CauchyCompletionMonadPacket_namecert_obligations [AskSetup] [PackageSetup]
    {sourceFamily windows observations schedule diagonal sealRow transport route nameRow :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionMonadPacket sourceFamily windows observations schedule diagonal sealRow
        transport route nameRow bundle pkg ->
      SemanticNameCert
        (fun row : BHist => hsame row sealRow ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
        (fun row : BHist => Cont schedule windows observations ∧
          Cont observations diagonal row)
        (fun row : BHist => PkgSig bundle row pkg ∧ Cont observations diagonal row)
        (fun row row' : BHist => hsame row row') := by
  intro packet
  obtain ⟨_sourceFamilyUnary, windowsUnary, scheduleUnary, diagonalUnary, _transportUnary,
    _nameRowUnary, scheduleWindowsObservations, observationsDiagonalSealRow,
    _sealRowTransportRoute, _routeNameSealRow, sealRowPkg⟩ := packet
  have observationsUnary : UnaryHistory observations :=
    unary_cont_closed scheduleUnary windowsUnary scheduleWindowsObservations
  have sealRowUnary : UnaryHistory sealRow :=
    unary_cont_closed observationsUnary diagonalUnary observationsDiagonalSealRow
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro sealRow ⟨hsame_refl sealRow, sealRowUnary, sealRowPkg⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same sourceRow
        cases same
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨scheduleWindowsObservations,
          cont_result_hsame_transport observationsDiagonalSealRow
            (hsame_symm sourceRow.left)⟩
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right.right,
          cont_result_hsame_transport observationsDiagonalSealRow
            (hsame_symm sourceRow.left)⟩
  }

theorem CauchyCompletionMonadPacket_diagonal_bind_stability [AskSetup] [PackageSetup]
    {sourceFamily windows observations schedule diagonal sealRow transport route nameRow
      sourceFamily' windows' observations' schedule' diagonal' sealRow' transport' route'
      nameRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionMonadPacket sourceFamily windows observations schedule diagonal sealRow
        transport route nameRow bundle pkg ->
      hsame sourceFamily sourceFamily' ->
        hsame windows windows' ->
          hsame schedule schedule' ->
            hsame diagonal diagonal' ->
              hsame transport transport' ->
                hsame nameRow nameRow' ->
                  Cont schedule' windows' observations' ->
                    Cont observations' diagonal' sealRow' ->
                      Cont sealRow' transport' route' ->
                        Cont route' nameRow' sealRow' ->
                          PkgSig bundle sealRow' pkg ->
                            CauchyCompletionMonadPacket sourceFamily' windows' observations'
                                schedule' diagonal' sealRow' transport' route' nameRow'
                                bundle pkg ∧
                              hsame observations observations' ∧ hsame sealRow sealRow' ∧
                                hsame route route' := by
  intro packet sameSourceFamily sameWindows sameSchedule sameDiagonal sameTransport sameNameRow
    scheduleWindowsObservations' observationsDiagonalSealRow' sealTransportRoute'
    routeNameSeal' sealRowPkg'
  obtain ⟨sourceFamilyUnary, windowsUnary, scheduleUnary, diagonalUnary, transportUnary,
    nameRowUnary, scheduleWindowsObservations, observationsDiagonalSealRow, sealTransportRoute,
    routeNameSeal, _sealRowPkg⟩ := packet
  have sourceFamilyUnary' : UnaryHistory sourceFamily' :=
    unary_transport sourceFamilyUnary sameSourceFamily
  have windowsUnary' : UnaryHistory windows' :=
    unary_transport windowsUnary sameWindows
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary sameSchedule
  have diagonalUnary' : UnaryHistory diagonal' :=
    unary_transport diagonalUnary sameDiagonal
  have transportUnary' : UnaryHistory transport' :=
    unary_transport transportUnary sameTransport
  have nameRowUnary' : UnaryHistory nameRow' :=
    unary_transport nameRowUnary sameNameRow
  have sameObservations : hsame observations observations' :=
    cont_respects_hsame sameSchedule sameWindows scheduleWindowsObservations
      scheduleWindowsObservations'
  have sameSealRow : hsame sealRow sealRow' :=
    cont_respects_hsame sameObservations sameDiagonal observationsDiagonalSealRow
      observationsDiagonalSealRow'
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameSealRow sameTransport sealTransportRoute sealTransportRoute'
  have targetPacket :
      CauchyCompletionMonadPacket sourceFamily' windows' observations' schedule' diagonal'
        sealRow' transport' route' nameRow' bundle pkg :=
    ⟨sourceFamilyUnary', windowsUnary', scheduleUnary', diagonalUnary', transportUnary',
      nameRowUnary', scheduleWindowsObservations', observationsDiagonalSealRow',
      sealTransportRoute', routeNameSeal', sealRowPkg'⟩
  exact ⟨targetPacket, sameObservations, sameSealRow, sameRoute⟩

theorem CauchyCompletionMonadPacket_public_real_seal_factorization [AskSetup]
    [PackageSetup]
    {sourceFamily windows observations schedule diagonal sealRow transport route nameRow :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionMonadPacket sourceFamily windows observations schedule diagonal sealRow
        transport route nameRow bundle pkg ->
      UnaryHistory observations ∧ UnaryHistory sealRow ∧ UnaryHistory route ∧
        hsame observations (append schedule windows) ∧
          hsame sealRow (append observations diagonal) ∧
            hsame route (append sealRow transport) ∧ PkgSig bundle sealRow pkg := by
  intro packet
  obtain ⟨_sourceFamilyUnary, windowsUnary, scheduleUnary, diagonalUnary, transportUnary,
    _nameRowUnary, scheduleWindowsObservations, observationsDiagonalSealRow,
    sealRowTransportRoute, _routeNameSealRow, sealRowPkg⟩ := packet
  have observationsUnary : UnaryHistory observations :=
    unary_cont_closed scheduleUnary windowsUnary scheduleWindowsObservations
  have sealRowUnary : UnaryHistory sealRow :=
    unary_cont_closed observationsUnary diagonalUnary observationsDiagonalSealRow
  have routeUnary : UnaryHistory route :=
    unary_cont_closed sealRowUnary transportUnary sealRowTransportRoute
  exact
    ⟨observationsUnary, sealRowUnary, routeUnary, scheduleWindowsObservations,
      observationsDiagonalSealRow, sealRowTransportRoute, sealRowPkg⟩

theorem CauchyCompletionMonadPacket_schedule_composition_boundary [AskSetup] [PackageSetup]
    {sourceFamily windows observations schedule diagonal sealRow transport route nameRow
      sourceFamily' windows' observations' schedule' diagonal' sealRow' transport' route'
      nameRow' composedSchedule composedObservations composedSeal composedRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionMonadPacket sourceFamily windows observations schedule diagonal sealRow
        transport route nameRow bundle pkg ->
      CauchyCompletionMonadPacket sourceFamily' windows' observations' schedule' diagonal'
          sealRow' transport' route' nameRow' bundle pkg ->
        Cont schedule schedule' composedSchedule ->
          Cont composedSchedule windows' composedObservations ->
            Cont composedObservations diagonal' composedSeal ->
              Cont composedSeal transport' composedRoute ->
                Cont composedRoute nameRow' composedSeal ->
                  PkgSig bundle composedSeal pkg ->
                    CauchyCompletionMonadPacket sourceFamily' windows' composedObservations
                        composedSchedule diagonal' composedSeal transport' composedRoute
                        nameRow' bundle pkg ∧
                      UnaryHistory composedSchedule ∧ UnaryHistory composedObservations ∧
                        UnaryHistory composedSeal ∧ UnaryHistory composedRoute ∧
                          PkgSig bundle composedSeal pkg := by
  intro leftPacket rightPacket scheduleSchedule'ComposedSchedule
    composedScheduleWindows'ComposedObservations composedObservationsDiagonal'ComposedSeal
    composedSealTransport'ComposedRoute composedRouteNameRow'ComposedSeal composedSealPkg
  obtain ⟨_sourceFamilyUnary, _windowsUnary, scheduleUnary, _diagonalUnary, _transportUnary,
    _nameRowUnary, _scheduleWindowsObservations, _observationsDiagonalSealRow,
    _sealRowTransportRoute, _routeNameRowSealRow, _sealRowPkg⟩ := leftPacket
  obtain ⟨sourceFamily'Unary, windows'Unary, schedule'Unary, diagonal'Unary, transport'Unary,
    nameRow'Unary, _schedule'Windows'Observations', _observations'Diagonal'SealRow',
    _sealRow'Transport'Route', _route'NameRow'SealRow', _sealRowPkg'⟩ := rightPacket
  have composedScheduleUnary : UnaryHistory composedSchedule :=
    unary_cont_closed scheduleUnary schedule'Unary scheduleSchedule'ComposedSchedule
  have composedObservationsUnary : UnaryHistory composedObservations :=
    unary_cont_closed composedScheduleUnary windows'Unary
      composedScheduleWindows'ComposedObservations
  have composedSealUnary : UnaryHistory composedSeal :=
    unary_cont_closed composedObservationsUnary diagonal'Unary
      composedObservationsDiagonal'ComposedSeal
  have composedRouteUnary : UnaryHistory composedRoute :=
    unary_cont_closed composedSealUnary transport'Unary composedSealTransport'ComposedRoute
  have targetPacket :
      CauchyCompletionMonadPacket sourceFamily' windows' composedObservations
        composedSchedule diagonal' composedSeal transport' composedRoute nameRow' bundle pkg :=
    ⟨sourceFamily'Unary, windows'Unary, composedScheduleUnary, diagonal'Unary,
      transport'Unary, nameRow'Unary, composedScheduleWindows'ComposedObservations,
      composedObservationsDiagonal'ComposedSeal, composedSealTransport'ComposedRoute,
      composedRouteNameRow'ComposedSeal, composedSealPkg⟩
  exact
    ⟨targetPacket, composedScheduleUnary, composedObservationsUnary, composedSealUnary,
      composedRouteUnary, composedSealPkg⟩

theorem CauchyCompletionMonadPacket_unit_boundary [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PkgSig bundle BHist.Empty pkg ->
      CauchyCompletionMonadPacket BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty bundle pkg ∧
        UnaryHistory BHist.Empty ∧ Cont BHist.Empty BHist.Empty BHist.Empty ∧
          PkgSig bundle BHist.Empty pkg := by
  intro emptyPkg
  have emptyPacket :
      CauchyCompletionMonadPacket BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty bundle pkg :=
    ⟨unary_empty, unary_empty, unary_empty, unary_empty, unary_empty, unary_empty,
      cont_left_unit BHist.Empty, cont_left_unit BHist.Empty, cont_left_unit BHist.Empty,
      cont_left_unit BHist.Empty, emptyPkg⟩
  exact ⟨emptyPacket, unary_empty, cont_left_unit BHist.Empty, emptyPkg⟩

end BEDC.Derived.CauchyCompletionMonadUp
