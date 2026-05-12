import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealLimitPacket [AskSetup] [PackageSetup]
    (schedule stream endpoint tolerance handoff route ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory schedule ∧ UnaryHistory stream ∧ UnaryHistory endpoint ∧
    UnaryHistory tolerance ∧ UnaryHistory handoff ∧ UnaryHistory route ∧
      UnaryHistory ledger ∧ Cont schedule stream handoff ∧ Cont handoff tolerance route ∧
        Cont route endpoint ledger ∧ PkgSig bundle ledger pkg

theorem RealLimitPacket_scheduled_handoff_transport [AskSetup] [PackageSetup]
    {schedule stream endpoint tolerance handoff route ledger schedule' stream' endpoint'
      tolerance' handoff' route' ledger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealLimitPacket schedule stream endpoint tolerance handoff route ledger bundle pkg ->
      hsame schedule schedule' ->
        hsame stream stream' ->
          hsame endpoint endpoint' ->
            hsame tolerance tolerance' ->
              Cont schedule' stream' handoff' ->
                Cont handoff' tolerance' route' ->
                  Cont route' endpoint' ledger' ->
                    PkgSig bundle ledger' pkg ->
                      RealLimitPacket schedule' stream' endpoint' tolerance' handoff' route'
                          ledger' bundle pkg ∧
                        hsame handoff handoff' ∧ hsame route route' ∧ hsame ledger ledger' := by
  intro packet sameSchedule sameStream sameEndpoint sameTolerance
  intro scheduledHandoff' toleranceRoute' endpointLedger' pkgLedger'
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport packet.left sameSchedule
  have streamUnary' : UnaryHistory stream' :=
    unary_transport packet.right.left sameStream
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport packet.right.right.left sameEndpoint
  have toleranceUnary' : UnaryHistory tolerance' :=
    unary_transport packet.right.right.right.left sameTolerance
  have handoffUnary' : UnaryHistory handoff' :=
    unary_cont_closed scheduleUnary' streamUnary' scheduledHandoff'
  have routeUnary' : UnaryHistory route' :=
    unary_cont_closed handoffUnary' toleranceUnary' toleranceRoute'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed routeUnary' endpointUnary' endpointLedger'
  have sameHandoff : hsame handoff handoff' :=
    cont_respects_hsame sameSchedule sameStream
      packet.right.right.right.right.right.right.right.left scheduledHandoff'
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameHandoff sameTolerance
      packet.right.right.right.right.right.right.right.right.left toleranceRoute'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameRoute sameEndpoint
      packet.right.right.right.right.right.right.right.right.right.left endpointLedger'
  have packet' :
      RealLimitPacket schedule' stream' endpoint' tolerance' handoff' route' ledger' bundle
        pkg :=
    ⟨scheduleUnary', streamUnary', endpointUnary', toleranceUnary', handoffUnary',
      routeUnary', ledgerUnary', scheduledHandoff', toleranceRoute', endpointLedger',
      pkgLedger'⟩
  exact ⟨packet', sameHandoff, sameRoute, sameLedger⟩

theorem RealLimitPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {schedule stream endpoint tolerance handoff route ledger schedule' stream' endpoint'
      tolerance' handoff' route' ledger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealLimitPacket schedule stream endpoint tolerance handoff route ledger bundle pkg ->
      RealLimitPacket schedule' stream' endpoint' tolerance' handoff' route' ledger' bundle pkg ->
        hsame schedule schedule' ->
          hsame stream stream' ->
            hsame tolerance tolerance' ->
              hsame endpoint endpoint' ->
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row ledger' ∧
                        RealLimitPacket schedule' stream' endpoint' tolerance' handoff' route'
                          row bundle pkg)
                    (fun row : BHist => UnaryHistory row ∧ Cont route' endpoint' row)
                    (fun row : BHist => PkgSig bundle row pkg ∧ UnaryHistory route')
                    (fun row row' : BHist => psame bundle pkg pkg ∧ hsame row row') ∧
                  hsame handoff handoff' ∧ hsame route route' ∧ hsame ledger ledger' := by
  intro packet packet' sameSchedule sameStream sameTolerance sameEndpoint
  have sameHandoff : hsame handoff handoff' :=
    cont_respects_hsame sameSchedule sameStream
      packet.right.right.right.right.right.right.right.left
      packet'.right.right.right.right.right.right.right.left
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameHandoff sameTolerance
      packet.right.right.right.right.right.right.right.right.left
      packet'.right.right.right.right.right.right.right.right.left
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameRoute sameEndpoint
      packet.right.right.right.right.right.right.right.right.right.left
      packet'.right.right.right.right.right.right.right.right.right.left
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row ledger' ∧
            RealLimitPacket schedule' stream' endpoint' tolerance' handoff' route' row bundle pkg)
        (fun row : BHist => UnaryHistory row ∧ Cont route' endpoint' row)
        (fun row : BHist => PkgSig bundle row pkg ∧ UnaryHistory route')
        (fun row row' : BHist => psame bundle pkg pkg ∧ hsame row row') := {
    core := {
      carrier_inhabited := Exists.intro ledger' ⟨hsame_refl ledger', packet'⟩
      equiv_refl := by
        intro row sourceRow
        obtain ⟨_sameRow, rowPacket⟩ := sourceRow
        obtain ⟨_scheduleUnary, _streamUnary, _endpointUnary, _toleranceUnary, _handoffUnary,
          _routeUnary, _rowUnary, _scheduledHandoff, _toleranceRoute, _endpointLedger,
          pkgRow⟩ := rowPacket
        exact ⟨PkgSig_psame_intro pkgRow pkgRow (hsame_refl row), hsame_refl row⟩
      equiv_symm := by
        intro _row _row' classified
        exact ⟨classified.left, hsame_symm classified.right⟩
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact ⟨leftClassified.left, hsame_trans leftClassified.right rightClassified.right⟩
      carrier_respects_equiv := by
        intro _row _row' classified sourceRow
        cases classified.right
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      obtain ⟨_sameRow, rowPacket⟩ := sourceRow
      obtain ⟨_scheduleUnary, _streamUnary, _endpointUnary, _toleranceUnary, _handoffUnary,
        _routeUnary, rowUnary, _scheduledHandoff, _toleranceRoute, endpointLedger,
        _pkgRow⟩ := rowPacket
      exact ⟨rowUnary, endpointLedger⟩
    ledger_sound := by
      intro _row sourceRow
      obtain ⟨_sameRow, rowPacket⟩ := sourceRow
      obtain ⟨_scheduleUnary, _streamUnary, _endpointUnary, _toleranceUnary, _handoffUnary,
        routeUnary, _rowUnary, _scheduledHandoff, _toleranceRoute, _endpointLedger,
        pkgRow⟩ := rowPacket
      exact ⟨pkgRow, routeUnary⟩
  }
  exact ⟨cert, sameHandoff, sameRoute, sameLedger⟩

theorem RealLimitPacket_readback_obligation [AskSetup] [PackageSetup]
    {schedule stream endpoint tolerance handoff route ledger readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealLimitPacket schedule stream endpoint tolerance handoff route ledger bundle pkg ->
      Cont endpoint tolerance readback ->
        UnaryHistory readback ∧ hsame readback (append endpoint tolerance) ∧
          UnaryHistory stream ∧ Cont schedule stream handoff ∧
            Cont handoff tolerance route ∧ Cont route endpoint ledger ∧
              PkgSig bundle ledger pkg := by
  intro packet readbackRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed packet.right.right.left packet.right.right.right.left readbackRow
  exact
    ⟨readbackUnary, readbackRow, packet.right.left,
      packet.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.right⟩

theorem RealLimitPacket_standard_bridge_boundary [AskSetup] [PackageSetup]
    {schedule stream endpoint tolerance handoff route ledger readback boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealLimitPacket schedule stream endpoint tolerance handoff route ledger bundle pkg ->
      Cont endpoint tolerance readback ->
        Cont ledger readback boundary ->
          PkgSig bundle boundary pkg ->
            UnaryHistory readback ∧ UnaryHistory boundary ∧
              hsame readback (append endpoint tolerance) ∧ Cont ledger readback boundary ∧
                PkgSig bundle boundary pkg := by
  intro packet readbackRow boundaryRow boundarySig
  have readbackData :=
    RealLimitPacket_readback_obligation packet readbackRow
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed packet.right.right.right.right.right.right.left readbackData.left
      boundaryRow
  exact
    ⟨readbackData.left, boundaryUnary, readbackData.right.left, boundaryRow, boundarySig⟩

end BEDC.Derived.RealLimitUp
