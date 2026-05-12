import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicApproximationCarrier [AskSetup] [PackageSetup]
    (precision endpoint window ledger provenance : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory endpoint ∧ UnaryHistory window ∧
    UnaryHistory ledger ∧ UnaryHistory provenance ∧ Cont precision endpoint window ∧
      Cont window ledger provenance ∧ PkgSig bundle provenance pkg

theorem DyadicApproximationCarrier_classifier_transport [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance precision' endpoint' window' ledger'
      provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      hsame precision precision' ->
        hsame endpoint endpoint' ->
          hsame ledger ledger' ->
            hsame provenance provenance' ->
              Cont precision' endpoint' window' ->
                Cont window' ledger' provenance' ->
                  DyadicApproximationCarrier precision' endpoint' window' ledger' provenance'
                      bundle pkg ∧
                    hsame window window' := by
  intro carrier samePrecision sameEndpoint sameLedger sameProvenance precisionEndpointWindow'
    windowLedgerProvenance'
  rcases carrier with
    ⟨precisionUnary, endpointUnary, windowUnary, ledgerUnary, provenanceUnary,
      precisionEndpointWindow, windowLedgerProvenance, pkgSig⟩
  have sameWindow : hsame window window' :=
    cont_respects_hsame samePrecision sameEndpoint precisionEndpointWindow
      precisionEndpointWindow'
  have precisionUnary' : UnaryHistory precision' :=
    unary_transport precisionUnary samePrecision
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport endpointUnary sameEndpoint
  have windowUnary' : UnaryHistory window' :=
    unary_transport windowUnary sameWindow
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_transport ledgerUnary sameLedger
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  cases sameProvenance
  exact And.intro
    (And.intro precisionUnary'
      (And.intro endpointUnary'
        (And.intro windowUnary'
          (And.intro ledgerUnary'
            (And.intro provenanceUnary'
              (And.intro precisionEndpointWindow'
                (And.intro windowLedgerProvenance' pkgSig)))))))
    sameWindow

theorem DyadicApproximationCarrier_common_precision_refinement [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance precision₂ endpoint₂ window₂ ledger₂
      provenance₂ common endpointCommon windowCommon ledgerCommon provenanceCommon : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      DyadicApproximationCarrier precision₂ endpoint₂ window₂ ledger₂ provenance₂ bundle pkg ->
        hsame precision common ->
          hsame precision₂ common ->
            hsame endpoint endpointCommon ->
              hsame endpoint₂ endpointCommon ->
                hsame ledger ledgerCommon ->
                  hsame ledger₂ ledgerCommon ->
                    hsame provenance provenanceCommon ->
                      hsame provenance₂ provenanceCommon ->
                        Cont common endpointCommon windowCommon ->
                          Cont windowCommon ledgerCommon provenanceCommon ->
                            DyadicApproximationCarrier common endpointCommon windowCommon
                                ledgerCommon provenanceCommon bundle pkg ∧
                              hsame window windowCommon ∧ hsame window₂ windowCommon := by
  intro leftCarrier rightCarrier samePrecision samePrecision₂ sameEndpoint sameEndpoint₂
    sameLedger sameLedger₂ sameProvenance sameProvenance₂ commonEndpointWindow
    commonWindowLedgerProvenance
  have leftRefined :
      DyadicApproximationCarrier common endpointCommon windowCommon ledgerCommon
          provenanceCommon bundle pkg ∧
        hsame window windowCommon :=
    DyadicApproximationCarrier_classifier_transport leftCarrier samePrecision sameEndpoint
      sameLedger sameProvenance commonEndpointWindow commonWindowLedgerProvenance
  have rightRefined :
      DyadicApproximationCarrier common endpointCommon windowCommon ledgerCommon
          provenanceCommon bundle pkg ∧
        hsame window₂ windowCommon :=
    DyadicApproximationCarrier_classifier_transport rightCarrier samePrecision₂ sameEndpoint₂
      sameLedger₂ sameProvenance₂ commonEndpointWindow commonWindowLedgerProvenance
  exact And.intro leftRefined.left (And.intro leftRefined.right rightRefined.right)

end BEDC.Derived.DyadicApproximationUp
