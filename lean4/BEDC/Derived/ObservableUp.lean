import BEDC.Derived.QuantumStateUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ObservableUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.QuantumStateUp

def ObservableBHistOperatorCarrier [AskSetup] [PackageSetup]
    (hilbert operator spectrum expectation witness provenance ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory hilbert ∧ UnaryHistory operator ∧ UnaryHistory spectrum ∧
    UnaryHistory expectation ∧ UnaryHistory witness ∧ UnaryHistory provenance ∧
      Cont operator spectrum expectation ∧ Cont hilbert witness ledger ∧
        Cont provenance ledger endpoint ∧ PkgSig bundle endpoint pkg

def ObservableSpectralExpectationClassifier [AskSetup] [PackageSetup]
    (hilbert operator spectrum expectation witness provenance ledger endpoint hilbert' operator'
      spectrum' expectation' witness' provenance' ledger' endpoint' : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance ledger
      endpoint bundle pkg ∧
    ObservableBHistOperatorCarrier hilbert' operator' spectrum' expectation' witness'
      provenance' ledger' endpoint' bundle pkg ∧
      hsame hilbert hilbert' ∧ hsame operator operator' ∧ hsame spectrum spectrum' ∧
        hsame expectation expectation' ∧ hsame witness witness' ∧
          hsame provenance provenance' ∧ hsame ledger ledger' ∧ hsame endpoint endpoint'

theorem ObservableBHistOperatorCarrier_quantumstate_expectation_boundary [AskSetup]
    [PackageSetup]
    {hilbert operator spectrum expectation witness provenance ledger endpoint stateHilbert
      stateProjective stateVector stateNorm statePhase stateProjectiveEndpoint stateHilbertLedger
      stateProjectiveLedger stateProvenance stateEndpoint expectationEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance ledger
        endpoint bundle pkg ->
      QuantumStateBHistCarrier stateHilbert stateProjective stateVector stateNorm statePhase
          stateProjectiveEndpoint stateHilbertLedger stateProjectiveLedger stateProvenance
          stateEndpoint bundle pkg ->
        hsame hilbert stateHilbert ->
          Cont operator stateEndpoint expectationEndpoint ->
            UnaryHistory expectationEndpoint ∧
              hsame expectationEndpoint (append operator stateEndpoint) ∧
                hsame endpoint (append provenance ledger) ∧ PkgSig bundle endpoint pkg := by
  intro operatorCarrier stateCarrier sameHilbert expectationRow
  have stateBoundary :=
    QuantumStateBHistCarrier_hilbert_source_boundary stateCarrier
  have projectiveLedgerRow :
      Cont stateProjective stateProjectiveEndpoint stateProjectiveLedger :=
    stateCarrier.right.right.right.right.right.right.right.right.left
  have endpointRow :
      Cont stateProvenance (append stateHilbertLedger stateProjectiveLedger) stateEndpoint :=
    stateCarrier.right.right.right.right.right.right.right.right.right.right.left
  have projectiveLedgerUnary : UnaryHistory stateProjectiveLedger :=
    unary_cont_closed stateCarrier.right.left stateCarrier.right.right.right.right.right.left
      projectiveLedgerRow
  have combinedLedgerUnary : UnaryHistory (append stateHilbertLedger stateProjectiveLedger) :=
    unary_append_closed stateBoundary.right.right.left projectiveLedgerUnary
  have stateEndpointUnary : UnaryHistory stateEndpoint :=
    unary_cont_closed stateCarrier.right.right.right.right.right.right.left combinedLedgerUnary
      endpointRow
  have _compatibleHilbert : hsame hilbert stateHilbert :=
    sameHilbert
  have expectationEndpointUnary : UnaryHistory expectationEndpoint :=
    unary_cont_closed operatorCarrier.right.left stateEndpointUnary expectationRow
  exact And.intro expectationEndpointUnary
    (And.intro expectationRow
      (And.intro operatorCarrier.right.right.right.right.right.right.right.right.left
        operatorCarrier.right.right.right.right.right.right.right.right.right))

theorem ObservableBHistOperatorCarrier_spectral_data_ledger [AskSetup] [PackageSetup]
    {hilbert operator spectrum expectation witness provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance ledger
        endpoint bundle pkg ->
      UnaryHistory expectation ∧ hsame expectation (append operator spectrum) ∧
        UnaryHistory ledger ∧ hsame ledger (append hilbert witness) ∧
          UnaryHistory endpoint ∧ hsame endpoint (append provenance ledger) ∧
            PkgSig bundle endpoint pkg := by
  intro carrier
  have expectationRow : Cont operator spectrum expectation :=
    carrier.right.right.right.right.right.right.left
  have ledgerRow : Cont hilbert witness ledger :=
    carrier.right.right.right.right.right.right.right.left
  have endpointRow : Cont provenance ledger endpoint :=
    carrier.right.right.right.right.right.right.right.right.left
  have expectationUnary : UnaryHistory expectation :=
    carrier.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed carrier.left carrier.right.right.right.right.left ledgerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed carrier.right.right.right.right.right.left ledgerUnary endpointRow
  exact And.intro expectationUnary
    (And.intro expectationRow
      (And.intro ledgerUnary
        (And.intro ledgerRow
          (And.intro endpointUnary
            (And.intro endpointRow
              carrier.right.right.right.right.right.right.right.right.right)))))

theorem ObservableBHistOperatorCarrier_hilbert_source_readback [AskSetup] [PackageSetup]
    {hilbert operator spectrum expectation witness provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance
        ledger endpoint bundle pkg ->
      UnaryHistory hilbert ∧ UnaryHistory operator ∧ UnaryHistory witness ∧
        Cont hilbert witness ledger ∧ Cont operator spectrum expectation ∧
          hsame ledger (append hilbert witness) ∧
            hsame expectation (append operator spectrum) ∧ PkgSig bundle endpoint pkg := by
  intro operatorCarrier
  have witnessUnary : UnaryHistory witness :=
    operatorCarrier.right.right.right.right.left
  have expectationRow : Cont operator spectrum expectation :=
    operatorCarrier.right.right.right.right.right.right.left
  have ledgerRow : Cont hilbert witness ledger :=
    operatorCarrier.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    operatorCarrier.right.right.right.right.right.right.right.right.right
  exact And.intro operatorCarrier.left
    (And.intro operatorCarrier.right.left
      (And.intro witnessUnary
        (And.intro ledgerRow
          (And.intro expectationRow
            (And.intro ledgerRow
              (And.intro expectationRow pkgSig))))))

theorem ObservableBHistOperatorCarrier_hilbert_source_boundary [AskSetup] [PackageSetup]
    {hilbert operator spectrum expectation witness provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance ledger
        endpoint bundle pkg ->
      UnaryHistory hilbert ∧ UnaryHistory operator ∧ UnaryHistory witness ∧
        UnaryHistory ledger ∧ UnaryHistory endpoint ∧ Cont hilbert witness ledger ∧
          hsame ledger (append hilbert witness) ∧ hsame endpoint (append provenance ledger) ∧
            PkgSig bundle endpoint pkg := by
  intro carrier
  have ledgerRow : Cont hilbert witness ledger :=
    carrier.right.right.right.right.right.right.right.left
  have endpointRow : Cont provenance ledger endpoint :=
    carrier.right.right.right.right.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed carrier.left carrier.right.right.right.right.left ledgerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed carrier.right.right.right.right.right.left ledgerUnary endpointRow
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro carrier.right.right.right.right.left
        (And.intro ledgerUnary
          (And.intro endpointUnary
            (And.intro ledgerRow
            (And.intro ledgerRow
              (And.intro endpointRow
                carrier.right.right.right.right.right.right.right.right.right)))))))

theorem ObservableBHistOperatorCarrier_hilbert_spectral_boundary [AskSetup] [PackageSetup]
    {hilbert operator spectrum expectation witness provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance ledger
        endpoint bundle pkg ->
      UnaryHistory hilbert ∧ UnaryHistory operator ∧ UnaryHistory spectrum ∧
        UnaryHistory expectation ∧ UnaryHistory witness ∧ UnaryHistory provenance ∧
          UnaryHistory ledger ∧ UnaryHistory endpoint ∧
            Cont operator spectrum expectation ∧ Cont hilbert witness ledger ∧
              Cont provenance ledger endpoint ∧ hsame expectation (append operator spectrum) ∧
                hsame ledger (append hilbert witness) ∧
                  hsame endpoint (append provenance ledger) ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  have expectationRow : Cont operator spectrum expectation :=
    carrier.right.right.right.right.right.right.left
  have ledgerRow : Cont hilbert witness ledger :=
    carrier.right.right.right.right.right.right.right.left
  have endpointRow : Cont provenance ledger endpoint :=
    carrier.right.right.right.right.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed carrier.left carrier.right.right.right.right.left ledgerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed carrier.right.right.right.right.right.left ledgerUnary endpointRow
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro carrier.right.right.left
        (And.intro carrier.right.right.right.left
          (And.intro carrier.right.right.right.right.left
            (And.intro carrier.right.right.right.right.right.left
              (And.intro ledgerUnary
                (And.intro endpointUnary
                  (And.intro expectationRow
                    (And.intro ledgerRow
                      (And.intro endpointRow
                        (And.intro expectationRow
                          (And.intro ledgerRow
                            (And.intro endpointRow
                              carrier.right.right.right.right.right.right.right.right.right)))))))))))))

theorem ObservableBHistOperatorCarrier_spectral_transport_stability [AskSetup]
    [PackageSetup]
    {hilbert operator operator' spectrum spectrum' expectation expectation' witness provenance
      ledger endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance ledger
        endpoint bundle pkg ->
      hsame operator operator' ->
        hsame spectrum spectrum' ->
          Cont operator' spectrum' expectation' ->
            Cont provenance ledger endpoint' ->
              PkgSig bundle endpoint' pkg ->
                ObservableBHistOperatorCarrier hilbert operator' spectrum' expectation' witness
                    provenance ledger endpoint' bundle pkg ∧
                  hsame expectation expectation' ∧ hsame endpoint endpoint' := by
  intro carrier sameOperator sameSpectrum expectationRow' endpointRow' pkgSig'
  have operatorUnary' : UnaryHistory operator' :=
    unary_transport carrier.right.left sameOperator
  have spectrumUnary' : UnaryHistory spectrum' :=
    unary_transport carrier.right.right.left sameSpectrum
  have expectationUnary' : UnaryHistory expectation' :=
    unary_cont_closed operatorUnary' spectrumUnary' expectationRow'
  have sameExpectation : hsame expectation expectation' :=
    cont_respects_hsame sameOperator sameSpectrum carrier.right.right.right.right.right.right.left
      expectationRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_deterministic carrier.right.right.right.right.right.right.right.right.left endpointRow'
  have carrier' :
      ObservableBHistOperatorCarrier hilbert operator' spectrum' expectation' witness provenance
        ledger endpoint' bundle pkg :=
    And.intro carrier.left
      (And.intro operatorUnary'
        (And.intro spectrumUnary'
          (And.intro expectationUnary'
            (And.intro carrier.right.right.right.right.left
              (And.intro carrier.right.right.right.right.right.left
                (And.intro expectationRow'
                  (And.intro carrier.right.right.right.right.right.right.right.left
                     (And.intro endpointRow' pkgSig'))))))))
  exact And.intro carrier' (And.intro sameExpectation sameEndpoint)

theorem ObservableBHistOperatorCarrier_expectation_ledger_exactness [AskSetup] [PackageSetup]
    {hilbert operator spectrum expectation witness provenance ledger endpoint expectationEndpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance ledger
        endpoint bundle pkg ->
      Cont operator expectation expectationEndpoint ->
        UnaryHistory expectationEndpoint ∧ hsame expectationEndpoint (append operator expectation) ∧
          UnaryHistory ledger ∧ hsame ledger (append hilbert witness) ∧
            hsame endpoint (append provenance ledger) ∧ PkgSig bundle endpoint pkg := by
  intro carrier expectationEndpointRow
  have ledgerRows :=
    ObservableBHistOperatorCarrier_spectral_data_ledger
      (hilbert := hilbert) (operator := operator) (spectrum := spectrum)
      (expectation := expectation) (witness := witness) (provenance := provenance)
      (ledger := ledger) (endpoint := endpoint) (bundle := bundle) (pkg := pkg) carrier
  have expectationEndpointUnary : UnaryHistory expectationEndpoint :=
    unary_cont_closed carrier.right.left carrier.right.right.right.left expectationEndpointRow
  exact And.intro expectationEndpointUnary
    (And.intro expectationEndpointRow
      (And.intro ledgerRows.right.right.left
        (And.intro ledgerRows.right.right.right.left
          (And.intro ledgerRows.right.right.right.right.right.left
            ledgerRows.right.right.right.right.right.right))))

theorem ObservableBHistOperatorCarrier_expectation_transport_exactness [AskSetup]
    [PackageSetup]
    {hilbert operator operator' spectrum spectrum' expectation expectation' witness provenance
      ledger endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance ledger
        endpoint bundle pkg ->
      hsame operator operator' ->
        hsame spectrum spectrum' ->
          Cont operator' spectrum' expectation' ->
            Cont provenance ledger endpoint' ->
              PkgSig bundle endpoint' pkg ->
                ObservableBHistOperatorCarrier hilbert operator' spectrum' expectation' witness
                    provenance ledger endpoint' bundle pkg ∧
                  UnaryHistory expectation' ∧ hsame expectation expectation' ∧
                    hsame endpoint endpoint' ∧ hsame expectation' (append operator' spectrum') := by
  intro carrier sameOperator sameSpectrum expectationRow' endpointRow' pkgSig'
  have transported :=
    ObservableBHistOperatorCarrier_spectral_transport_stability carrier sameOperator sameSpectrum
      expectationRow' endpointRow' pkgSig'
  have exactReadback :=
    ObservableBHistOperatorCarrier_spectral_data_ledger transported.left
  exact And.intro transported.left
    (And.intro exactReadback.left
      (And.intro transported.right.left
        (And.intro transported.right.right
          exactReadback.right.left)))

theorem ObservableBHistOperatorCarrier_public_consumer_exhaustion [AskSetup] [PackageSetup]
    {hilbert operator spectrum expectation witness provenance ledger endpoint expectationEndpoint
      consumerEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance ledger
        endpoint bundle pkg ->
      Cont operator expectation expectationEndpoint ->
        Cont expectationEndpoint endpoint consumerEndpoint ->
          UnaryHistory consumerEndpoint ∧
            hsame consumerEndpoint (append (append operator expectation) endpoint) ∧
              hsame endpoint (append provenance ledger) ∧ PkgSig bundle endpoint pkg := by
  intro carrier expectationEndpointRow consumerEndpointRow
  have exactness :=
    ObservableBHistOperatorCarrier_expectation_ledger_exactness
      (hilbert := hilbert) (operator := operator) (spectrum := spectrum)
      (expectation := expectation) (witness := witness) (provenance := provenance)
      (ledger := ledger) (endpoint := endpoint) (expectationEndpoint := expectationEndpoint)
      (bundle := bundle) (pkg := pkg) carrier expectationEndpointRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed carrier.right.right.right.right.right.left exactness.right.right.left
      carrier.right.right.right.right.right.right.right.right.left
  have consumerEndpointUnary : UnaryHistory consumerEndpoint :=
    unary_cont_closed exactness.left endpointUnary consumerEndpointRow
  have consumerReadback : hsame consumerEndpoint (append (append operator expectation) endpoint) :=
    hsame_trans consumerEndpointRow (congrArg (fun row : BHist => append row endpoint) exactness.right.left)
  exact And.intro consumerEndpointUnary
    (And.intro consumerReadback
      (And.intro exactness.right.right.right.right.left
        exactness.right.right.right.right.right))

theorem ObservableBHistOperatorCarrier_expectation_pairing_boundary [AskSetup] [PackageSetup]
    {hilbert operator spectrum expectation witness provenance ledger endpoint stateHilbert
      stateProjective stateVector stateNorm statePhase stateProjectiveEndpoint stateHilbertLedger
      stateProjectiveLedger stateProvenance stateEndpoint expectationEndpoint consumerEndpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance ledger
        endpoint bundle pkg ->
      QuantumStateBHistCarrier stateHilbert stateProjective stateVector stateNorm statePhase
          stateProjectiveEndpoint stateHilbertLedger stateProjectiveLedger stateProvenance
          stateEndpoint bundle pkg ->
        hsame hilbert stateHilbert ->
          Cont operator stateEndpoint expectationEndpoint ->
            Cont expectationEndpoint endpoint consumerEndpoint ->
              UnaryHistory expectationEndpoint ∧
                hsame expectationEndpoint (append operator stateEndpoint) ∧
                  UnaryHistory consumerEndpoint ∧
                    hsame consumerEndpoint (append expectationEndpoint endpoint) ∧
                      hsame endpoint (append provenance ledger) ∧
                        PkgSig bundle endpoint pkg := by
  intro carrier stateCarrier sameHilbert expectationRow consumerRow
  have expectationBoundary :=
    ObservableBHistOperatorCarrier_quantumstate_expectation_boundary
      (hilbert := hilbert) (operator := operator) (spectrum := spectrum)
      (expectation := expectation) (witness := witness) (provenance := provenance)
      (ledger := ledger) (endpoint := endpoint) (stateHilbert := stateHilbert)
      (stateProjective := stateProjective) (stateVector := stateVector)
      (stateNorm := stateNorm) (statePhase := statePhase)
      (stateProjectiveEndpoint := stateProjectiveEndpoint)
      (stateHilbertLedger := stateHilbertLedger)
      (stateProjectiveLedger := stateProjectiveLedger) (stateProvenance := stateProvenance)
      (stateEndpoint := stateEndpoint) (expectationEndpoint := expectationEndpoint)
      (bundle := bundle) (pkg := pkg) carrier stateCarrier sameHilbert expectationRow
  have spectralRows :=
    ObservableBHistOperatorCarrier_spectral_data_ledger
      (hilbert := hilbert) (operator := operator) (spectrum := spectrum)
      (expectation := expectation) (witness := witness) (provenance := provenance)
      (ledger := ledger) (endpoint := endpoint) (bundle := bundle) (pkg := pkg) carrier
  have consumerUnary : UnaryHistory consumerEndpoint :=
    unary_cont_closed expectationBoundary.left spectralRows.right.right.right.right.left
      consumerRow
  exact And.intro expectationBoundary.left
    (And.intro expectationBoundary.right.left
      (And.intro consumerUnary
        (And.intro consumerRow
          (And.intro expectationBoundary.right.right.left expectationBoundary.right.right.right))))

theorem ObservableBHistOperatorCarrier_expectation_row_transport_composition [AskSetup]
    [PackageSetup]
    {hilbert operator operator' spectrum spectrum' expectation expectation' witness provenance
      ledger endpoint endpoint' expectationEndpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance ledger
        endpoint bundle pkg ->
      hsame operator operator' ->
        hsame spectrum spectrum' ->
          Cont operator' spectrum' expectation' ->
            Cont provenance ledger endpoint' ->
              PkgSig bundle endpoint' pkg ->
                Cont operator' expectation' expectationEndpoint' ->
                  ObservableBHistOperatorCarrier hilbert operator' spectrum' expectation' witness
                      provenance ledger endpoint' bundle pkg ∧
                    UnaryHistory expectationEndpoint' ∧
                      hsame expectationEndpoint' (append operator' expectation') ∧
                        hsame endpoint endpoint' ∧ PkgSig bundle endpoint' pkg := by
  intro carrier sameOperator sameSpectrum expectationRow' endpointRow' pkgSig' expectationEndpointRow'
  have transported :=
    ObservableBHistOperatorCarrier_expectation_transport_exactness carrier sameOperator sameSpectrum
      expectationRow' endpointRow' pkgSig'
  have expectationEndpointUnary : UnaryHistory expectationEndpoint' :=
    unary_cont_closed transported.left.right.left transported.left.right.right.right.left
      expectationEndpointRow'
  exact And.intro transported.left
    (And.intro expectationEndpointUnary
      (And.intro expectationEndpointRow'
        (And.intro transported.right.right.right.left pkgSig')))

theorem ObservableBHistOperatorCarrier_operator_row_classifier_determinacy [AskSetup]
    [PackageSetup]
    {hilbert hilbert' operator operator' spectrum spectrum' expectation expectation' witness
      witness' provenance provenance' ledger ledger' endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance ledger
        endpoint bundle pkg ->
      ObservableBHistOperatorCarrier hilbert' operator' spectrum' expectation' witness' provenance'
          ledger' endpoint' bundle pkg ->
        hsame hilbert hilbert' ->
          hsame operator operator' ->
            hsame spectrum spectrum' ->
              hsame witness witness' ->
                hsame provenance provenance' ->
                  hsame expectation expectation' ∧ hsame ledger ledger' ∧
                    hsame endpoint endpoint' := by
  intro carrier carrier' sameHilbert sameOperator sameSpectrum sameWitness sameProvenance
  have sameExpectation : hsame expectation expectation' :=
    cont_respects_hsame sameOperator sameSpectrum
      carrier.right.right.right.right.right.right.left
      carrier'.right.right.right.right.right.right.left
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameHilbert sameWitness
      carrier.right.right.right.right.right.right.right.left
      carrier'.right.right.right.right.right.right.right.left
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameLedger
      carrier.right.right.right.right.right.right.right.right.left
      carrier'.right.right.right.right.right.right.right.right.left
  exact And.intro sameExpectation (And.intro sameLedger sameEndpoint)

theorem ObservableBHistOperatorCarrier_classifier_stability [AskSetup] [PackageSetup]
    {hilbert operator operator' spectrum spectrum' expectation expectation' witness witness'
      provenance provenance' ledger ledger' endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance ledger
        endpoint bundle pkg ->
      hsame operator operator' ->
        hsame spectrum spectrum' ->
          hsame witness witness' ->
            hsame provenance provenance' ->
              Cont operator' spectrum' expectation' ->
                Cont hilbert witness' ledger' ->
                  Cont provenance' ledger' endpoint' ->
                    PkgSig bundle endpoint' pkg ->
                      ObservableBHistOperatorCarrier hilbert operator' spectrum' expectation'
                          witness' provenance' ledger' endpoint' bundle pkg ∧
                        hsame expectation expectation' ∧ hsame ledger ledger' ∧
                          hsame endpoint endpoint' := by
  intro carrier sameOperator sameSpectrum sameWitness sameProvenance expectationRow' ledgerRow'
    endpointRow' pkgSig'
  have operatorUnary' : UnaryHistory operator' :=
    unary_transport carrier.right.left sameOperator
  have spectrumUnary' : UnaryHistory spectrum' :=
    unary_transport carrier.right.right.left sameSpectrum
  have witnessUnary' : UnaryHistory witness' :=
    unary_transport carrier.right.right.right.right.left sameWitness
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport carrier.right.right.right.right.right.left sameProvenance
  have expectationUnary' : UnaryHistory expectation' :=
    unary_cont_closed operatorUnary' spectrumUnary' expectationRow'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed carrier.left witnessUnary' ledgerRow'
  have sameExpectation : hsame expectation expectation' :=
    cont_respects_hsame sameOperator sameSpectrum
      carrier.right.right.right.right.right.right.left expectationRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame (hsame_refl hilbert) sameWitness
      carrier.right.right.right.right.right.right.right.left ledgerRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameLedger
      carrier.right.right.right.right.right.right.right.right.left endpointRow'
  exact And.intro
    (And.intro carrier.left
      (And.intro operatorUnary'
        (And.intro spectrumUnary'
          (And.intro expectationUnary'
            (And.intro witnessUnary'
              (And.intro provenanceUnary'
                (And.intro expectationRow'
                  (And.intro ledgerRow'
                    (And.intro endpointRow' pkgSig')))))))))
    (And.intro sameExpectation (And.intro sameLedger sameEndpoint))

theorem ObservableBHistOperatorCarrier_hilbert_spectral_ledger_exactness [AskSetup]
    [PackageSetup]
    {hilbert operator spectrum expectation witness provenance ledger endpoint spectralEndpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance ledger
        endpoint bundle pkg ->
      Cont spectrum witness spectralEndpoint ->
        UnaryHistory hilbert ∧ UnaryHistory operator ∧ UnaryHistory spectrum ∧
          UnaryHistory expectation ∧ UnaryHistory witness ∧ UnaryHistory spectralEndpoint ∧
            hsame expectation (append operator spectrum) ∧
              hsame spectralEndpoint (append spectrum witness) ∧
                hsame endpoint (append provenance ledger) ∧ PkgSig bundle endpoint pkg := by
  intro carrier spectralEndpointRow
  have endpointRow : Cont provenance ledger endpoint :=
    carrier.right.right.right.right.right.right.right.right.left
  have spectralEndpointUnary : UnaryHistory spectralEndpoint :=
    unary_cont_closed carrier.right.right.left carrier.right.right.right.right.left
      spectralEndpointRow
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro carrier.right.right.left
        (And.intro carrier.right.right.right.left
          (And.intro carrier.right.right.right.right.left
            (And.intro spectralEndpointUnary
                (And.intro carrier.right.right.right.right.right.right.left
                  (And.intro spectralEndpointRow
                    (And.intro endpointRow
                      carrier.right.right.right.right.right.right.right.right.right))))))))

theorem ObservableBHistOperatorCarrier_dependency_namecert_exactness [AskSetup] [PackageSetup]
    {hilbert operator spectrum expectation witness provenance ledger endpoint
      expectationEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance ledger
        endpoint bundle pkg ->
      Cont operator expectation expectationEndpoint ->
        UnaryHistory hilbert ∧ UnaryHistory spectrum ∧ UnaryHistory expectation ∧
          UnaryHistory expectationEndpoint ∧ Cont operator spectrum expectation ∧
            Cont hilbert witness ledger ∧ Cont provenance ledger endpoint ∧
              hsame expectationEndpoint (append operator expectation) ∧
                hsame endpoint (append provenance ledger) ∧ PkgSig bundle endpoint pkg := by
  intro carrier expectationEndpointRow
  have expectationEndpointUnary : UnaryHistory expectationEndpoint :=
    unary_cont_closed carrier.right.left carrier.right.right.right.left expectationEndpointRow
  exact And.intro carrier.left
    (And.intro carrier.right.right.left
      (And.intro carrier.right.right.right.left
        (And.intro expectationEndpointUnary
          (And.intro carrier.right.right.right.right.right.right.left
            (And.intro carrier.right.right.right.right.right.right.right.left
              (And.intro carrier.right.right.right.right.right.right.right.right.left
                (And.intro expectationEndpointRow
                  (And.intro carrier.right.right.right.right.right.right.right.right.left
                    carrier.right.right.right.right.right.right.right.right.right))))))))

theorem ObservableBHistOperatorCarrier_public_row_family [AskSetup] [PackageSetup]
    {hilbert operator spectrum expectation witness provenance ledger endpoint expectationEndpoint
      consumerEndpoint spectralEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObservableBHistOperatorCarrier hilbert operator spectrum expectation witness provenance ledger
        endpoint bundle pkg ->
      Cont operator expectation expectationEndpoint ->
        Cont expectationEndpoint endpoint consumerEndpoint ->
          Cont spectrum witness spectralEndpoint ->
            SemanticNameCert (fun h : BHist => hsame h endpoint)
                (fun h : BHist => hsame h endpoint) (fun h : BHist => hsame h endpoint)
                hsame ∧
              UnaryHistory consumerEndpoint ∧ UnaryHistory spectralEndpoint ∧
                hsame consumerEndpoint (append (append operator expectation) endpoint) ∧
                  hsame spectralEndpoint (append spectrum witness) ∧
                    PkgSig bundle endpoint pkg := by
  intro carrier expectationEndpointRow consumerEndpointRow spectralEndpointRow
  have publicRows :=
    ObservableBHistOperatorCarrier_public_consumer_exhaustion
      (hilbert := hilbert) (operator := operator) (spectrum := spectrum)
      (expectation := expectation) (witness := witness) (provenance := provenance)
      (ledger := ledger) (endpoint := endpoint) (expectationEndpoint := expectationEndpoint)
      (consumerEndpoint := consumerEndpoint) (bundle := bundle) (pkg := pkg)
      carrier expectationEndpointRow consumerEndpointRow
  have spectralRows :=
    ObservableBHistOperatorCarrier_hilbert_spectral_ledger_exactness
      (hilbert := hilbert) (operator := operator) (spectrum := spectrum)
      (expectation := expectation) (witness := witness) (provenance := provenance)
      (ledger := ledger) (endpoint := endpoint) (spectralEndpoint := spectralEndpoint)
      (bundle := bundle) (pkg := pkg) carrier spectralEndpointRow
  have core :
      NameCert (fun h : BHist => hsame h endpoint) hsame := {
    carrier_inhabited := Exists.intro endpoint (hsame_refl endpoint)
    equiv_refl := by
      intro h _source
      exact hsame_refl h
    equiv_symm := by
      intro h k sameHK
      exact hsame_symm sameHK
    equiv_trans := by
      intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    carrier_respects_equiv := by
      intro h k sameHK sourceH
      exact hsame_trans (hsame_symm sameHK) sourceH
  }
  have cert :
      SemanticNameCert (fun h : BHist => hsame h endpoint)
        (fun h : BHist => hsame h endpoint) (fun h : BHist => hsame h endpoint) hsame := {
    core := core
    pattern_sound := by
      intro h source
      exact source
    ledger_sound := by
      intro h source
      exact source
  }
  exact And.intro cert
    (And.intro publicRows.left
      (And.intro spectralRows.right.right.right.right.right.left
        (And.intro publicRows.right.left
          (And.intro spectralRows.right.right.right.right.right.right.right.left
            publicRows.right.right.right))))

end BEDC.Derived.ObservableUp
