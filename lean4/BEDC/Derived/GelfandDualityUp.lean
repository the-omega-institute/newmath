import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.CstaralgebraUp

namespace BEDC.Derived.GelfandDualityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.CstaralgebraUp

def GelfandDualitySpectrumPairingCarrier [AskSetup] [PackageSetup]
    (A X character evaluation rhoA rhoX provenance ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory A ∧ UnaryHistory X ∧ UnaryHistory character ∧ UnaryHistory evaluation ∧
    UnaryHistory provenance ∧ hsame rhoA A ∧ hsame rhoX X ∧
      Cont character evaluation ledger ∧ Cont ledger provenance endpoint ∧
        Cont provenance ledger endpoint ∧ PkgSig bundle endpoint pkg

def GelfandDualitySpectrumTransportPackage [AskSetup] [PackageSetup]
    (A X character evaluation rhoA rhoX provenance ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  GelfandDualitySpectrumPairingCarrier A X character evaluation rhoA rhoX provenance
      ledger endpoint bundle pkg ∧
    ∃ evaluationProvenance : BHist,
      Cont evaluation provenance evaluationProvenance ∧
        Cont character evaluationProvenance endpoint

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

theorem GelfandDualitySpectrumTransportPackage_exactness [AskSetup] [PackageSetup]
    {A X character evaluation rhoA rhoX provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GelfandDualitySpectrumPairingCarrier A X character evaluation rhoA rhoX provenance
        ledger endpoint bundle pkg ->
      GelfandDualitySpectrumTransportPackage A X character evaluation rhoA rhoX provenance
        ledger endpoint bundle pkg := by
  intro carrier
  have characterEvaluationLedger : Cont character evaluation ledger :=
    carrier.right.right.right.right.right.right.right.left
  have ledgerProvenanceEndpoint : Cont ledger provenance endpoint :=
    carrier.right.right.right.right.right.right.right.right.left
  cases cont_assoc_middle_exists characterEvaluationLedger ledgerProvenanceEndpoint with
  | intro evaluationProvenance route =>
      exact And.intro carrier (Exists.intro evaluationProvenance route)

theorem GelfandDualitySpectrumPairingCarrier_namecert_obligation_surface
    [AskSetup] [PackageSetup]
    {A X character evaluation rhoA rhoX provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GelfandDualitySpectrumPairingCarrier A X character evaluation rhoA rhoX provenance
        ledger endpoint bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint) hsame ∧
        UnaryHistory A ∧ UnaryHistory X ∧ UnaryHistory character ∧
          UnaryHistory evaluation ∧ hsame rhoA A ∧ hsame rhoX X ∧
            Cont character evaluation ledger ∧ Cont provenance ledger endpoint ∧
              PkgSig bundle endpoint pkg := by
  intro carrier
  have endpointSelf : hsame endpoint endpoint :=
    hsame_refl endpoint
  have cert :
      SemanticNameCert (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint) hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSelf
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row other target sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other sameRows rowSource
        exact hsame_trans (hsame_symm sameRows) rowSource
    }
    pattern_sound := by
      intro row source
      exact source
    ledger_sound := by
      intro row source
      exact source
  }
  exact And.intro cert
    (And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro carrier.right.right.left
          (And.intro carrier.right.right.right.left
            (And.intro carrier.right.right.right.right.right.left
              (And.intro carrier.right.right.right.right.right.right.left
                (And.intro carrier.right.right.right.right.right.right.right.left
                  (And.intro carrier.right.right.right.right.right.right.right.right.right.left
                    carrier.right.right.right.right.right.right.right.right.right.right))))))))

theorem GelfandDualitySpectrumPairingCarrier_topology_consumer_boundary
    [AskSetup] [PackageSetup]
    {A X character evaluation rhoA rhoX provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GelfandDualitySpectrumPairingCarrier A X character evaluation rhoA rhoX provenance
        ledger endpoint bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row X)
          (fun row : BHist => hsame row X) (fun row : BHist => hsame row X) hsame ∧
        UnaryHistory X ∧ UnaryHistory character ∧ UnaryHistory evaluation ∧ hsame rhoX X ∧
          Cont character evaluation ledger ∧ Cont ledger provenance endpoint ∧
            Cont provenance ledger endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  have cert :
      SemanticNameCert (fun row : BHist => hsame row X)
          (fun row : BHist => hsame row X) (fun row : BHist => hsame row X) hsame := {
    core := {
      carrier_inhabited := Exists.intro X (hsame_refl X)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row other target sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other sameRows rowSource
        exact hsame_trans (hsame_symm sameRows) rowSource
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro carrier.right.left
      (And.intro carrier.right.right.left
        (And.intro carrier.right.right.right.left
          (And.intro carrier.right.right.right.right.right.right.left
            (And.intro carrier.right.right.right.right.right.right.right.left
              (And.intro carrier.right.right.right.right.right.right.right.right.left
                (And.intro carrier.right.right.right.right.right.right.right.right.right.left
                  carrier.right.right.right.right.right.right.right.right.right.right)))))))

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

theorem GelfandDualitySpectrumPairingCarrier_cstaralgebra_consumer_boundary
    [AskSetup] [PackageSetup]
    {A X character evaluation rhoA rhoX provenance ledger endpoint : BHist}
    {banach ring mul involution normSquare carrierTransport multiplicationTransport
      involutionTransport normTransport cstarLedger cstarEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GelfandDualitySpectrumPairingCarrier A X character evaluation rhoA rhoX provenance
        ledger endpoint bundle pkg ->
      CstaralgebraBHistCarrier banach ring mul involution normSquare carrierTransport
        multiplicationTransport involutionTransport normTransport provenance cstarLedger
        cstarEndpoint bundle pkg ->
        hsame A banach ->
          UnaryHistory A ∧ UnaryHistory character ∧ UnaryHistory evaluation ∧
            hsame rhoA A ∧ Cont character evaluation ledger ∧ UnaryHistory banach ∧
              UnaryHistory ring ∧ hsame A banach ∧ PkgSig bundle endpoint pkg := by
  intro spectrum cstar sameABanach
  have unaryA : UnaryHistory A :=
    spectrum.left
  have unaryCharacter : UnaryHistory character :=
    spectrum.right.right.left
  have unaryEvaluation : UnaryHistory evaluation :=
    spectrum.right.right.right.left
  have rhoASame : hsame rhoA A :=
    spectrum.right.right.right.right.right.left
  have characterEvaluationLedger : Cont character evaluation ledger :=
    spectrum.right.right.right.right.right.right.right.left
  have spectrumPkg : PkgSig bundle endpoint pkg :=
    spectrum.right.right.right.right.right.right.right.right.right.right
  have unaryBanach : UnaryHistory banach :=
    cstar.left
  have unaryRing : UnaryHistory ring :=
    cstar.right.left
  exact And.intro unaryA
    (And.intro unaryCharacter
      (And.intro unaryEvaluation
        (And.intro rhoASame
          (And.intro characterEvaluationLedger
            (And.intro unaryBanach
              (And.intro unaryRing
                (And.intro sameABanach spectrumPkg)))))))

end BEDC.Derived.GelfandDualityUp
