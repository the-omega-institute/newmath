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

end BEDC.Derived.BeliefUp
