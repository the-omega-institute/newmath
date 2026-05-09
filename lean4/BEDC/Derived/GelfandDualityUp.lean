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

theorem GelfandDualitySpectrumPairingCarrier_spectrum_ledger_exactness [AskSetup]
    [PackageSetup] {A X character evaluation rhoA rhoX provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GelfandDualitySpectrumPairingCarrier A X character evaluation rhoA rhoX provenance
        ledger endpoint bundle pkg ->
      UnaryHistory A ∧ UnaryHistory X ∧ UnaryHistory character ∧ UnaryHistory evaluation ∧
        UnaryHistory provenance ∧ Cont character evaluation ledger ∧
          Cont ledger provenance endpoint ∧ Cont provenance ledger endpoint ∧
            hsame ledger (append character evaluation) ∧
              hsame endpoint (append ledger provenance) ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  have characterRow : Cont character evaluation ledger :=
    carrier.right.right.right.right.right.right.right.left
  have endpointRow : Cont ledger provenance endpoint :=
    carrier.right.right.right.right.right.right.right.right.left
  exact
    ⟨carrier.left, carrier.right.left, carrier.right.right.left,
      carrier.right.right.right.left, carrier.right.right.right.right.left, characterRow,
      endpointRow, carrier.right.right.right.right.right.right.right.right.right.left,
      characterRow, endpointRow,
      carrier.right.right.right.right.right.right.right.right.right.right⟩

theorem GelfandDualitySpectrumPairingCarrier_classifier_stability [AskSetup] [PackageSetup]
    {A X character evaluation rhoA rhoX provenance ledger endpoint A' X' character'
      evaluation' provenance' ledger' endpoint' : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    GelfandDualitySpectrumPairingCarrier A X character evaluation rhoA rhoX provenance ledger
        endpoint bundle pkg ->
      hsame A A' -> hsame X X' -> hsame character character' ->
        hsame evaluation evaluation' -> hsame provenance provenance' ->
          Cont character' evaluation' ledger' -> Cont ledger' provenance' endpoint' ->
            Cont provenance' ledger' endpoint' -> PkgSig bundle endpoint' pkg ->
              GelfandDualitySpectrumPairingCarrier A' X' character' evaluation' rhoA rhoX
                  provenance' ledger' endpoint' bundle pkg ∧ hsame ledger ledger' ∧
                hsame endpoint endpoint' := by
  intro carrier sameA sameX sameCharacter sameEvaluation sameProvenance ledgerCont'
    endpointCont' provenanceEndpointCont' pkgSig'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameCharacter sameEvaluation
      carrier.right.right.right.right.right.right.right.left ledgerCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameLedger sameProvenance
      carrier.right.right.right.right.right.right.right.right.left endpointCont'
  have transported :
      GelfandDualitySpectrumPairingCarrier A' X' character' evaluation' rhoA rhoX
          provenance' ledger' endpoint' bundle pkg :=
    ⟨unary_transport carrier.left sameA,
      unary_transport carrier.right.left sameX,
      unary_transport carrier.right.right.left sameCharacter,
      unary_transport carrier.right.right.right.left sameEvaluation,
      unary_transport carrier.right.right.right.right.left sameProvenance,
      hsame_trans carrier.right.right.right.right.right.left sameA,
      hsame_trans carrier.right.right.right.right.right.right.left sameX,
      ledgerCont',
      endpointCont',
      provenanceEndpointCont',
      pkgSig'⟩
  exact And.intro transported (And.intro sameLedger sameEndpoint)

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
