import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ContinuedFractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ContinuedFractionPacket [AskSetup] [PackageSetup]
    (digits numer denom radius schedule handoff boundary ledger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory digits ∧ UnaryHistory numer ∧ UnaryHistory denom ∧ UnaryHistory radius ∧
    UnaryHistory schedule ∧ UnaryHistory handoff ∧ UnaryHistory boundary ∧
      UnaryHistory ledger ∧ UnaryHistory provenance ∧ Cont schedule numer handoff ∧
        Cont handoff ledger boundary ∧ Cont boundary schedule provenance ∧
          PkgSig bundle provenance pkg

theorem ContinuedFractionPacket_recurrence_ledger_transport [AskSetup] [PackageSetup]
    {digits numer denom radius schedule handoff boundary ledger provenance recurrence recurrence'
      window window' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuedFractionPacket digits numer denom radius schedule handoff boundary ledger provenance
        bundle pkg ->
      Cont numer denom recurrence -> hsame recurrence recurrence' ->
        Cont recurrence radius window -> Cont recurrence' radius window' ->
          UnaryHistory recurrence' ∧ UnaryHistory window' ∧ hsame window window' ∧
            PkgSig bundle provenance pkg := by
  intro packet recurrenceRow sameRecurrence windowRow windowRow'
  obtain ⟨_digitsUnary, numerUnary, denomUnary, radiusUnary, _scheduleUnary, _handoffUnary,
    _boundaryUnary, _ledgerUnary, _provenanceUnary, _scheduleNumerRow, _boundaryRow,
    _provenanceRow, pkgSig⟩ := packet
  have recurrenceUnary : UnaryHistory recurrence :=
    unary_cont_closed numerUnary denomUnary recurrenceRow
  have recurrenceUnary' : UnaryHistory recurrence' :=
    unary_transport recurrenceUnary sameRecurrence
  have windowUnary' : UnaryHistory window' :=
    unary_cont_closed recurrenceUnary' radiusUnary windowRow'
  have sameWindow : hsame window window' :=
    cont_respects_hsame sameRecurrence (hsame_refl radius) windowRow windowRow'
  exact ⟨recurrenceUnary', windowUnary', sameWindow, pkgSig⟩

theorem ContinuedFractionPacket_real_boundary_transport [AskSetup] [PackageSetup]
    {digits numer denom radius schedule handoff boundary ledger provenance handoff'
      boundary' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuedFractionPacket digits numer denom radius schedule handoff boundary ledger provenance
        bundle pkg ->
      hsame handoff handoff' -> Cont handoff' ledger boundary' ->
      UnaryHistory boundary' ∧ hsame boundary boundary' ∧ PkgSig bundle provenance pkg := by
  intro packet sameHandoff boundaryRow'
  obtain ⟨_digitsUnary, _numerUnary, _denomUnary, _radiusUnary, _scheduleUnary, handoffUnary,
    _boundaryUnary, ledgerUnary, _provenanceUnary, _scheduleNumerRow, boundaryRow,
    _provenanceRow, pkgSig⟩ := packet
  have handoffUnary' : UnaryHistory handoff' :=
    unary_transport handoffUnary sameHandoff
  have boundaryUnary' : UnaryHistory boundary' :=
    unary_cont_closed handoffUnary' ledgerUnary boundaryRow'
  have sameBoundary : hsame boundary boundary' :=
    cont_respects_hsame sameHandoff (hsame_refl ledger) boundaryRow boundaryRow'
  exact ⟨boundaryUnary', sameBoundary, pkgSig⟩

theorem ContinuedFractionPacket_regseqrat_handoff [AskSetup] [PackageSetup]
    {digits numerator denominator radius schedule handoff boundary ledger provenance consumer :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuedFractionPacket digits numerator denominator radius schedule handoff boundary ledger
        provenance bundle pkg ->
      Cont handoff boundary consumer ->
        PkgSig bundle provenance pkg ->
          UnaryHistory digits ∧ UnaryHistory numerator ∧ UnaryHistory denominator ∧
            UnaryHistory radius ∧ UnaryHistory schedule ∧ UnaryHistory handoff ∧
              UnaryHistory consumer ∧ Cont schedule numerator handoff ∧
                Cont handoff boundary consumer ∧ PkgSig bundle provenance pkg := by
  intro packet consumerRow pkgRow
  obtain ⟨digitsUnary, numeratorUnary, denominatorUnary, radiusUnary, scheduleUnary,
    handoffUnary, boundaryUnary, _ledgerUnary, _provenanceUnary, scheduleNumeratorRow,
    _boundaryRow, _provenanceRow, _storedPkgRow⟩ := packet
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed handoffUnary boundaryUnary consumerRow
  exact ⟨digitsUnary, numeratorUnary, denominatorUnary, radiusUnary, scheduleUnary, handoffUnary,
    consumerUnary, scheduleNumeratorRow, consumerRow, pkgRow⟩

theorem ContinuedFractionPacket_finite_handoff_obligation [AskSetup] [PackageSetup]
    {digits numerator denominator radius schedule handoff boundary ledger provenance consumer
      readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuedFractionPacket digits numerator denominator radius schedule handoff boundary ledger
        provenance bundle pkg ->
      Cont schedule handoff consumer ->
        Cont consumer provenance readback ->
          PkgSig bundle readback pkg ->
            UnaryHistory schedule ∧ UnaryHistory handoff ∧ UnaryHistory ledger ∧
              UnaryHistory provenance ∧ UnaryHistory consumer ∧ UnaryHistory readback ∧
                Cont schedule handoff consumer ∧ Cont consumer provenance readback ∧
                  PkgSig bundle readback pkg := by
  intro packet consumerRow readbackRow readbackPkg
  obtain ⟨_digitsUnary, _numeratorUnary, _denominatorUnary, _radiusUnary, scheduleUnary,
    handoffUnary, _boundaryUnary, ledgerUnary, provenanceUnary, _scheduleNumeratorRow,
    _boundaryRow, _provenanceRow, _packetPkg⟩ := packet
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed scheduleUnary handoffUnary consumerRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed consumerUnary provenanceUnary readbackRow
  exact
    ⟨scheduleUnary, handoffUnary, ledgerUnary, provenanceUnary, consumerUnary, readbackUnary,
      consumerRow, readbackRow, readbackPkg⟩

theorem ContinuedFractionPacket_convergent_window_standard_bridge [AskSetup] [PackageSetup]
    {digits numerator denominator radius schedule handoff boundary ledger provenance recurrence
      window consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuedFractionPacket digits numerator denominator radius schedule handoff boundary ledger
        provenance bundle pkg ->
      Cont numerator denominator recurrence ->
        Cont recurrence radius window ->
          Cont handoff boundary consumer ->
            PkgSig bundle consumer pkg ->
              UnaryHistory digits ∧ UnaryHistory numerator ∧ UnaryHistory denominator ∧
                UnaryHistory radius ∧ UnaryHistory schedule ∧ UnaryHistory recurrence ∧
                  UnaryHistory window ∧ UnaryHistory consumer ∧
                    Cont schedule numerator handoff ∧ Cont numerator denominator recurrence ∧
                      Cont recurrence radius window ∧ Cont handoff boundary consumer ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  intro packet numeratorDenominatorRecurrence recurrenceRadiusWindow handoffBoundaryConsumer
    consumerPkg
  obtain ⟨digitsUnary, numeratorUnary, denominatorUnary, radiusUnary, scheduleUnary,
    handoffUnary, boundaryUnary, _ledgerUnary, _provenanceUnary, scheduleNumeratorHandoff,
    _handoffLedgerBoundary, _boundaryScheduleProvenance, provenancePkg⟩ := packet
  have recurrenceUnary : UnaryHistory recurrence :=
    unary_cont_closed numeratorUnary denominatorUnary numeratorDenominatorRecurrence
  have windowUnary : UnaryHistory window :=
    unary_cont_closed recurrenceUnary radiusUnary recurrenceRadiusWindow
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed handoffUnary boundaryUnary handoffBoundaryConsumer
  exact
    ⟨digitsUnary, numeratorUnary, denominatorUnary, radiusUnary, scheduleUnary, recurrenceUnary,
      windowUnary, consumerUnary, scheduleNumeratorHandoff, numeratorDenominatorRecurrence,
      recurrenceRadiusWindow, handoffBoundaryConsumer, provenancePkg, consumerPkg⟩

end BEDC.Derived.ContinuedFractionUp
