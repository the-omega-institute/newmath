import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.RealLimitUp
