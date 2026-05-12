import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ModulusOfConvergenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ModulusOfConvergenceCarrier [AskSetup] [PackageSetup]
    (precision selector modulus schedule witness ledger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory selector ∧ UnaryHistory modulus ∧
    UnaryHistory schedule ∧ UnaryHistory witness ∧ UnaryHistory ledger ∧
      UnaryHistory provenance ∧ Cont precision selector modulus ∧
        Cont modulus schedule witness ∧ Cont witness ledger provenance ∧
          PkgSig bundle provenance pkg

theorem ModulusOfConvergenceCarrier_composition_stability [AskSetup] [PackageSetup]
    {precision selector modulus schedule witness ledger provenance precision' selector' modulus'
      schedule' witness' ledger' provenance' : BHist}
    {bundle bundle' : ProbeBundle ProbeName} {pkg pkg' : Pkg} :
    ModulusOfConvergenceCarrier precision selector modulus schedule witness ledger provenance
        bundle pkg ->
      ModulusOfConvergenceCarrier precision' selector' modulus' schedule' witness' ledger'
        provenance' bundle' pkg' ->
        exists joined : BHist, Cont provenance precision' joined ∧ UnaryHistory joined := by
  intro leftCarrier rightCarrier
  cases leftCarrier with
  | intro _precisionUnary leftRest =>
      cases leftRest with
      | intro _selectorUnary leftRest =>
          cases leftRest with
          | intro _modulusUnary leftRest =>
              cases leftRest with
              | intro _scheduleUnary leftRest =>
                  cases leftRest with
                  | intro _witnessUnary leftRest =>
                      cases leftRest with
                      | intro _ledgerUnary leftRest =>
                          cases leftRest with
                          | intro provenanceUnary _leftRows =>
                              cases rightCarrier with
                              | intro precisionUnary' _rightRest =>
                                  let joined := append provenance precision'
                                  have joinedRow : Cont provenance precision' joined := by
                                    rfl
                                  have joinedUnary : UnaryHistory joined :=
                                    unary_repetition_closed_under_continuation provenanceUnary
                                      precisionUnary' joinedRow
                                  exact ⟨joined, joinedRow, joinedUnary⟩

def ModulusOfConvergencePacket
    (precision threshold modulus schedule late ledger provenance : BHist) : Prop :=
  UnaryHistory precision ∧ UnaryHistory threshold ∧ UnaryHistory schedule ∧
    UnaryHistory late ∧ Cont precision threshold modulus ∧ Cont schedule late ledger ∧
      Cont modulus ledger provenance

theorem ModulusOfConvergencePacket_ledger_exactness
    {precision threshold modulus schedule late ledger provenance : BHist} :
    ModulusOfConvergencePacket precision threshold modulus schedule late ledger provenance ->
      UnaryHistory precision ∧ UnaryHistory threshold ∧ UnaryHistory schedule ∧
        UnaryHistory late ∧ UnaryHistory modulus ∧ UnaryHistory ledger ∧
          UnaryHistory provenance ∧ hsame modulus (append precision threshold) ∧
            hsame ledger (append schedule late) ∧
              hsame provenance (append modulus ledger) := by
  intro packet
  have precisionUnary : UnaryHistory precision := packet.left
  have thresholdUnary : UnaryHistory threshold := packet.right.left
  have scheduleUnary : UnaryHistory schedule := packet.right.right.left
  have lateUnary : UnaryHistory late := packet.right.right.right.left
  have modulusCont : Cont precision threshold modulus := packet.right.right.right.right.left
  have ledgerCont : Cont schedule late ledger := packet.right.right.right.right.right.left
  have provenanceCont : Cont modulus ledger provenance := packet.right.right.right.right.right.right
  have modulusUnary : UnaryHistory modulus :=
    unary_cont_closed precisionUnary thresholdUnary modulusCont
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed scheduleUnary lateUnary ledgerCont
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed modulusUnary ledgerUnary provenanceCont
  constructor
  · exact precisionUnary
  constructor
  · exact thresholdUnary
  constructor
  · exact scheduleUnary
  constructor
  · exact lateUnary
  constructor
  · exact modulusUnary
  constructor
  · exact ledgerUnary
  constructor
  · exact provenanceUnary
  constructor
  · exact modulusCont
  constructor
  · exact ledgerCont
  · exact provenanceCont

def ModulusOfConvergenceRatePacket [AskSetup] [PackageSetup]
    (precision selector modulus schedule witness ledger provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory selector ∧ UnaryHistory schedule ∧
    UnaryHistory witness ∧ UnaryHistory provenance ∧ Cont precision selector modulus ∧
      Cont schedule witness ledger ∧ Cont modulus ledger endpoint ∧
        PkgSig bundle endpoint pkg

theorem ModulusOfConvergenceRatePacket_tail_restriction_stability [AskSetup] [PackageSetup]
    {precision selector modulus schedule witness ledger provenance endpoint tail restrictedSchedule
      restrictedLedger restrictedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModulusOfConvergenceRatePacket precision selector modulus schedule witness ledger provenance
        endpoint bundle pkg ->
      UnaryHistory tail ->
        Cont schedule tail restrictedSchedule ->
          Cont restrictedSchedule witness restrictedLedger ->
            Cont modulus restrictedLedger restrictedEndpoint ->
              PkgSig bundle restrictedEndpoint pkg ->
                ModulusOfConvergenceRatePacket precision selector modulus restrictedSchedule witness
                    restrictedLedger provenance restrictedEndpoint bundle pkg ∧
                  hsame restrictedSchedule (append schedule tail) ∧
                    hsame restrictedLedger (append restrictedSchedule witness) := by
  intro packet tailUnary restrictedScheduleRow restrictedLedgerRow restrictedEndpointRow pkgSig
  have precisionUnary : UnaryHistory precision :=
    packet.left
  have selectorUnary : UnaryHistory selector :=
    packet.right.left
  have scheduleUnary : UnaryHistory schedule :=
    packet.right.right.left
  have witnessUnary : UnaryHistory witness :=
    packet.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    packet.right.right.right.right.left
  have modulusRow : Cont precision selector modulus :=
    packet.right.right.right.right.right.left
  have modulusUnary : UnaryHistory modulus :=
    unary_cont_closed precisionUnary selectorUnary modulusRow
  have restrictedScheduleUnary : UnaryHistory restrictedSchedule :=
    unary_cont_closed scheduleUnary tailUnary restrictedScheduleRow
  have restrictedLedgerUnary : UnaryHistory restrictedLedger :=
    unary_cont_closed restrictedScheduleUnary witnessUnary restrictedLedgerRow
  have _restrictedEndpointUnary : UnaryHistory restrictedEndpoint :=
    unary_cont_closed modulusUnary restrictedLedgerUnary restrictedEndpointRow
  have restrictedPacket :
      ModulusOfConvergenceRatePacket precision selector modulus restrictedSchedule witness
        restrictedLedger provenance restrictedEndpoint bundle pkg :=
    And.intro precisionUnary
      (And.intro selectorUnary
        (And.intro restrictedScheduleUnary
          (And.intro witnessUnary
            (And.intro provenanceUnary
              (And.intro modulusRow
                (And.intro restrictedLedgerRow
                  (And.intro restrictedEndpointRow pkgSig)))))))
  exact And.intro restrictedPacket
    (And.intro restrictedScheduleRow restrictedLedgerRow)

end BEDC.Derived.ModulusOfConvergenceUp
