import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.GelfandDualityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def GelfandDualitySpectrumPairingCarrier [AskSetup] [PackageSetup]
    (A X character evaluation rhoA rhoX provenance ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory A ∧ UnaryHistory X ∧ UnaryHistory character ∧ UnaryHistory evaluation ∧
    UnaryHistory provenance ∧ hsame rhoA A ∧ hsame rhoX X ∧
      Cont character evaluation ledger ∧ Cont ledger provenance endpoint ∧
        Cont provenance ledger endpoint ∧ PkgSig bundle endpoint pkg

theorem GelfandDualitySpectrum_source_obligation [AskSetup] [PackageSetup]
    {A X character evaluation rhoA rhoX provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GelfandDualitySpectrumPairingCarrier A X character evaluation rhoA rhoX provenance
        ledger endpoint bundle pkg ->
      UnaryHistory A ∧ UnaryHistory X ∧ UnaryHistory character ∧ UnaryHistory evaluation ∧
        hsame rhoA A ∧ hsame rhoX X ∧ Cont character evaluation ledger ∧
          Cont ledger provenance endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  exact
    ⟨carrier.left, carrier.right.left, carrier.right.right.left,
      carrier.right.right.right.left, carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.right⟩

theorem GelfandDualitySpectrumPairingCarrier_source_obligation [AskSetup] [PackageSetup]
    {A X character evaluation rhoA rhoX provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GelfandDualitySpectrumPairingCarrier A X character evaluation rhoA rhoX provenance
        ledger endpoint bundle pkg ->
      UnaryHistory A ∧ UnaryHistory X ∧ UnaryHistory character ∧ UnaryHistory evaluation ∧
        hsame rhoA A ∧ hsame rhoX X ∧ Cont character evaluation ledger ∧
          Cont provenance ledger endpoint ∧ hsame endpoint (append provenance ledger) := by
  intro carrier
  exact
    ⟨carrier.left, carrier.right.left, carrier.right.right.left,
      carrier.right.right.right.left, carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.left⟩

theorem GelfandDualitySpectrumPairingCarrier_evaluation_ledger_determinacy
    [AskSetup] [PackageSetup]
    {A X character evaluation evaluation' rhoA rhoX provenance provenance' ledger ledger'
      endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GelfandDualitySpectrumPairingCarrier A X character evaluation rhoA rhoX provenance
        ledger endpoint bundle pkg ->
      GelfandDualitySpectrumPairingCarrier A X character evaluation' rhoA rhoX provenance'
        ledger' endpoint' bundle pkg ->
      hsame evaluation evaluation' ->
      hsame provenance provenance' ->
      hsame ledger ledger' ∧ hsame endpoint endpoint' ∧
        hsame (append provenance ledger) (append provenance' ledger') := by
  intro leftCarrier rightCarrier sameEvaluation sameProvenance
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame (hsame_refl character) sameEvaluation
      leftCarrier.right.right.right.right.right.right.right.left
      rightCarrier.right.right.right.right.right.right.right.left
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameLedger
      leftCarrier.right.right.right.right.right.right.right.right.right.left
      rightCarrier.right.right.right.right.right.right.right.right.right.left
  have sameDisplayedLedger :
      hsame (append provenance ledger) (append provenance' ledger') :=
    cont_respects_hsame sameProvenance sameLedger (cont_intro rfl) (cont_intro rfl)
  exact ⟨sameLedger, sameEndpoint, sameDisplayedLedger⟩

end BEDC.Derived.GelfandDualityUp
