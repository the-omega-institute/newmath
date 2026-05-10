import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BeliefUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BeliefObservationUpdateCarrier [AskSetup] [PackageSetup]
    (prior observation updateTrace probability evidence posterior : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory prior ∧ UnaryHistory observation ∧ UnaryHistory updateTrace ∧
    UnaryHistory probability ∧ Cont prior observation updateTrace ∧
      Cont updateTrace probability posterior ∧
        Cont prior (append observation (append updateTrace probability)) evidence ∧
          PkgSig bundle evidence pkg

theorem BeliefObservationUpdateCarrier_transport_obligation [AskSetup] [PackageSetup]
    {prior observation updateTrace probability evidence posterior prior' observation' updateTrace'
      probability' evidence' posterior' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BeliefObservationUpdateCarrier prior observation updateTrace probability evidence posterior
        bundle pkg ->
      hsame prior' prior -> hsame observation' observation -> hsame updateTrace' updateTrace ->
        hsame probability' probability -> Cont prior' observation' updateTrace' ->
          Cont updateTrace' probability' posterior' ->
            Cont prior' (append observation' (append updateTrace' probability')) evidence' ->
              PkgSig bundle evidence' pkg ->
                BeliefObservationUpdateCarrier prior' observation' updateTrace' probability'
                    evidence' posterior' bundle pkg ∧
                  hsame updateTrace updateTrace' ∧ hsame posterior posterior' ∧
                    hsame evidence evidence' := by
  intro carrier samePrior' sameObservation' sameUpdate' sameProbability' updateRow'
  intro posteriorRow' evidenceRow' pkgSig'
  have priorUnary' : UnaryHistory prior' :=
    unary_transport carrier.left (hsame_symm samePrior')
  have observationUnary' : UnaryHistory observation' :=
    unary_transport carrier.right.left (hsame_symm sameObservation')
  have updateUnary' : UnaryHistory updateTrace' :=
    unary_transport carrier.right.right.left (hsame_symm sameUpdate')
  have probabilityUnary' : UnaryHistory probability' :=
    unary_transport carrier.right.right.right.left (hsame_symm sameProbability')
  have sameUpdate : hsame updateTrace updateTrace' :=
    cont_respects_hsame (hsame_symm samePrior') (hsame_symm sameObservation')
      carrier.right.right.right.right.left updateRow'
  have samePosterior : hsame posterior posterior' :=
    cont_respects_hsame sameUpdate (hsame_symm sameProbability')
      carrier.right.right.right.right.right.left posteriorRow'
  have sameProbability : hsame probability probability' :=
    hsame_symm sameProbability'
  have updateProbabilitySame :
      hsame (append updateTrace probability) (append updateTrace' probability') :=
    cont_respects_hsame sameUpdate sameProbability
      (rfl : Cont updateTrace probability (append updateTrace probability))
      (rfl : Cont updateTrace' probability' (append updateTrace' probability'))
  have evidenceTailSame :
      hsame (append observation (append updateTrace probability))
        (append observation' (append updateTrace' probability')) :=
    cont_respects_hsame (hsame_symm sameObservation') updateProbabilitySame
      (rfl : Cont observation (append updateTrace probability)
        (append observation (append updateTrace probability)))
      (rfl : Cont observation' (append updateTrace' probability')
        (append observation' (append updateTrace' probability')))
  have sameEvidence : hsame evidence evidence' :=
    cont_respects_hsame (hsame_symm samePrior') evidenceTailSame
      carrier.right.right.right.right.right.right.left evidenceRow'
  exact
    ⟨⟨priorUnary', observationUnary', updateUnary', probabilityUnary', updateRow',
        posteriorRow', evidenceRow', pkgSig'⟩, sameUpdate, samePosterior, sameEvidence⟩

theorem BeliefObservationUpdateCarrier_classifier_transport [AskSetup] [PackageSetup]
    {prior prior' observation observation' updateTrace updateTrace' probability probability'
      evidence evidence' posterior posterior' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BeliefObservationUpdateCarrier prior observation updateTrace probability evidence posterior
        bundle pkg ->
      hsame prior prior' -> hsame observation observation' -> hsame updateTrace updateTrace' ->
        hsame probability probability' -> Cont prior' observation' updateTrace' ->
          Cont updateTrace' probability' posterior' ->
            Cont prior' (append observation' (append updateTrace' probability')) evidence' ->
              PkgSig bundle evidence' pkg ->
                BeliefObservationUpdateCarrier prior' observation' updateTrace' probability'
                    evidence' posterior' bundle pkg ∧
                  hsame posterior posterior' ∧ hsame evidence evidence' := by
  intro carrier samePrior sameObservation sameUpdate sameProbability updateRow'
  intro posteriorRow' evidenceRow' pkgSig'
  have transported :=
    BeliefObservationUpdateCarrier_transport_obligation carrier (hsame_symm samePrior)
      (hsame_symm sameObservation) (hsame_symm sameUpdate) (hsame_symm sameProbability)
      updateRow' posteriorRow' evidenceRow' pkgSig'
  exact ⟨transported.left, transported.right.right.left, transported.right.right.right⟩

theorem BeliefObservationUpdateCarrier_ledger_exactness [AskSetup] [PackageSetup]
    {prior observation trace probability ledger posterior : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BeliefObservationUpdateCarrier prior observation trace probability ledger posterior
        bundle pkg ->
      UnaryHistory ledger ∧
        hsame ledger (append prior (append observation (append trace probability))) ∧
          hsame trace (append prior observation) ∧
            hsame posterior (append trace probability) := by
  intro carrier
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed carrier.left carrier.right.left carrier.right.right.right.right.left
  have posteriorUnary : UnaryHistory posterior :=
    unary_cont_closed traceUnary carrier.right.right.right.left
      carrier.right.right.right.right.right.left
  have traceProbabilityUnary : UnaryHistory (append trace probability) :=
    unary_cont_closed traceUnary carrier.right.right.right.left
      (rfl : Cont trace probability (append trace probability))
  have evidenceTailUnary :
      UnaryHistory (append observation (append trace probability)) :=
    unary_cont_closed carrier.right.left traceProbabilityUnary
      (rfl : Cont observation (append trace probability)
        (append observation (append trace probability)))
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed carrier.left evidenceTailUnary
      carrier.right.right.right.right.right.right.left
  exact
    ⟨ledgerUnary, carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.left, carrier.right.right.right.right.right.left⟩

theorem BeliefObservationUpdateCarrier_tastegate_carrier_recognition [AskSetup] [PackageSetup]
    {prior observation updateTrace probability evidence posterior : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BeliefObservationUpdateCarrier prior observation updateTrace probability evidence posterior
        bundle pkg ->
      UnaryHistory prior ∧ UnaryHistory observation ∧ UnaryHistory updateTrace ∧
        UnaryHistory probability ∧ UnaryHistory posterior ∧ UnaryHistory evidence ∧
          Cont prior observation updateTrace ∧ Cont updateTrace probability posterior ∧
            PkgSig bundle evidence pkg := by
  intro carrier
  have posteriorUnary : UnaryHistory posterior :=
    unary_cont_closed carrier.right.right.left carrier.right.right.right.left
      carrier.right.right.right.right.right.left
  have updateProbabilityUnary : UnaryHistory (append updateTrace probability) :=
    unary_cont_closed carrier.right.right.left carrier.right.right.right.left
      (rfl : Cont updateTrace probability (append updateTrace probability))
  have evidenceTailUnary :
      UnaryHistory (append observation (append updateTrace probability)) :=
    unary_cont_closed carrier.right.left updateProbabilityUnary
      (rfl : Cont observation (append updateTrace probability)
        (append observation (append updateTrace probability)))
  have evidenceUnary : UnaryHistory evidence :=
    unary_cont_closed carrier.left evidenceTailUnary
      carrier.right.right.right.right.right.right.left
  exact
    ⟨carrier.left, carrier.right.left, carrier.right.right.left,
      carrier.right.right.right.left, posteriorUnary, evidenceUnary,
        carrier.right.right.right.right.left, carrier.right.right.right.right.right.left,
          carrier.right.right.right.right.right.right.right⟩

theorem BeliefObservationUpdateCarrier_finite_evidence_ledger_coverage [AskSetup]
    [PackageSetup] {prior observation updateTrace probability evidence posterior : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BeliefObservationUpdateCarrier prior observation updateTrace probability evidence posterior
        bundle pkg ->
      UnaryHistory posterior ∧ UnaryHistory evidence ∧
        hsame updateTrace (append prior observation) ∧
          hsame posterior (append updateTrace probability) ∧
            hsame evidence (append prior (append observation (append updateTrace probability))) ∧
              PkgSig bundle evidence pkg := by
  intro carrier
  have ledgerExact :=
    BeliefObservationUpdateCarrier_ledger_exactness
      (prior := prior) (observation := observation) (trace := updateTrace)
      (probability := probability) (ledger := evidence) (posterior := posterior)
      (bundle := bundle) (pkg := pkg) carrier
  have posteriorUnary : UnaryHistory posterior :=
    unary_cont_closed carrier.right.right.left carrier.right.right.right.left
      carrier.right.right.right.right.right.left
  exact
    ⟨posteriorUnary, ledgerExact.left, ledgerExact.right.right.left,
      ledgerExact.right.right.right, ledgerExact.right.left,
      carrier.right.right.right.right.right.right.right⟩

end BEDC.Derived.BeliefUp
