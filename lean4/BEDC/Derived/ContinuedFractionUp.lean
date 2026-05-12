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
      UnaryHistory ledger ∧ Cont handoff ledger boundary ∧ Cont boundary schedule provenance ∧
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
  have numerUnary : UnaryHistory numer := packet.right.left
  have denomUnary : UnaryHistory denom := packet.right.right.left
  have radiusUnary : UnaryHistory radius := packet.right.right.right.left
  have pkgSig : PkgSig bundle provenance pkg :=
    packet.right.right.right.right.right.right.right.right.right.right
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
  have handoffUnary : UnaryHistory handoff := packet.right.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger := packet.right.right.right.right.right.right.right.left
  have boundaryRow : Cont handoff ledger boundary :=
    packet.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle provenance pkg :=
    packet.right.right.right.right.right.right.right.right.right.right
  have handoffUnary' : UnaryHistory handoff' :=
    unary_transport handoffUnary sameHandoff
  have boundaryUnary' : UnaryHistory boundary' :=
    unary_cont_closed handoffUnary' ledgerUnary boundaryRow'
  have sameBoundary : hsame boundary boundary' :=
    cont_respects_hsame sameHandoff (hsame_refl ledger) boundaryRow boundaryRow'
  exact ⟨boundaryUnary', sameBoundary, pkgSig⟩

end BEDC.Derived.ContinuedFractionUp
