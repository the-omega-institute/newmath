import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicApproximationCarrier [AskSetup] [PackageSetup]
    (precision endpoint window ledger provenance : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory endpoint ∧ UnaryHistory window ∧
    UnaryHistory ledger ∧ UnaryHistory provenance ∧ Cont precision endpoint window ∧
      Cont window ledger provenance ∧ PkgSig bundle provenance pkg

theorem DyadicApproximationCarrier_precision_window_determinacy [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance candidate candidate' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      Cont precision endpoint candidate -> Cont precision endpoint candidate' ->
        hsame window candidate ∧ hsame window candidate' ∧ UnaryHistory candidate ∧
          UnaryHistory candidate' ∧ PkgSig bundle provenance pkg := by
  intro carrier precisionEndpointCandidate precisionEndpointCandidate'
  rcases carrier with
    ⟨precisionUnary, endpointUnary, windowUnary, ledgerUnary, provenanceUnary,
      precisionEndpointWindow, windowLedgerProvenance, pkgSig⟩
  have sameCandidate : hsame window candidate :=
    cont_deterministic precisionEndpointWindow precisionEndpointCandidate
  have sameCandidate' : hsame window candidate' :=
    cont_deterministic precisionEndpointWindow precisionEndpointCandidate'
  have candidateUnary : UnaryHistory candidate :=
    unary_cont_closed precisionUnary endpointUnary precisionEndpointCandidate
  have candidateUnary' : UnaryHistory candidate' :=
    unary_cont_closed precisionUnary endpointUnary precisionEndpointCandidate'
  exact And.intro sameCandidate
    (And.intro sameCandidate'
      (And.intro candidateUnary (And.intro candidateUnary' pkgSig)))

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

theorem DyadicApproximationCarrier_real_seal_radius_route_certificate [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance coarser endpoint2 window2 ledger2 provenance2
      sealRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      hsame precision coarser ->
        hsame endpoint endpoint2 ->
          hsame ledger ledger2 ->
            hsame provenance provenance2 ->
              Cont coarser endpoint2 window2 ->
                Cont window2 ledger2 provenance2 ->
                  Cont ledger2 provenance2 sealRow ->
                    PkgSig bundle sealRow pkg ->
                      SemanticNameCert
                        (fun row : BHist =>
                          hsame row sealRow ∧ UnaryHistory row ∧
                            Cont ledger2 provenance2 row ∧ PkgSig bundle row pkg)
                        (fun row : BHist =>
                          UnaryHistory coarser ∧ UnaryHistory endpoint2 ∧
                            UnaryHistory window2 ∧ Cont coarser endpoint2 window2 ∧
                              Cont window2 ledger2 provenance2 ∧
                                Cont ledger2 provenance2 row)
                        (fun row : BHist =>
                          PkgSig bundle row pkg ∧ hsame provenance provenance2 ∧
                            hsame endpoint endpoint2)
                        (fun row row' : BHist => psame bundle pkg pkg ∧ hsame row row') := by
  intro carrier samePrecision sameEndpoint sameLedger sameProvenance
    coarserEndpointWindow windowLedgerProvenance sealRoute sealPkg
  obtain ⟨precisionUnary, endpointUnary, _windowUnary, ledgerUnary, provenanceUnary,
    _precisionEndpointWindow, _windowLedgerProvenance, _pkgSig⟩ := carrier
  have coarserUnary : UnaryHistory coarser :=
    unary_transport precisionUnary samePrecision
  have endpoint2Unary : UnaryHistory endpoint2 :=
    unary_transport endpointUnary sameEndpoint
  have ledger2Unary : UnaryHistory ledger2 :=
    unary_transport ledgerUnary sameLedger
  have provenance2Unary : UnaryHistory provenance2 :=
    unary_transport provenanceUnary sameProvenance
  have window2Unary : UnaryHistory window2 :=
    unary_cont_closed coarserUnary endpoint2Unary coarserEndpointWindow
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed ledger2Unary provenance2Unary sealRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro sealRow ⟨hsame_refl sealRow, sealUnary, sealRoute, sealPkg⟩
      equiv_refl := by
        intro row sourceRow
        exact ⟨PkgSig_psame_intro sourceRow.right.right.right sourceRow.right.right.right
          (hsame_refl row), hsame_refl row⟩
      equiv_symm := by
        intro _row _row' classified
        exact ⟨classified.left, hsame_symm classified.right⟩
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact ⟨leftClassified.left, hsame_trans leftClassified.right rightClassified.right⟩
      carrier_respects_equiv := by
        intro _row _row' classified sourceRow
        cases classified.right
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨coarserUnary, endpoint2Unary, window2Unary, coarserEndpointWindow,
          windowLedgerProvenance, sourceRow.right.right.left⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right.right, sameProvenance, sameEndpoint⟩
  }

theorem DyadicApproximationCarrier_real_seal_handoff [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance sealRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      Cont ledger provenance sealRow ->
        PkgSig bundle sealRow pkg ->
          UnaryHistory precision ∧ UnaryHistory endpoint ∧ UnaryHistory window ∧
            UnaryHistory ledger ∧ UnaryHistory provenance ∧ UnaryHistory sealRow ∧
              Cont precision endpoint window ∧ Cont window ledger provenance ∧
                Cont ledger provenance sealRow ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle sealRow pkg := by
  intro carrier ledgerProvenanceSeal sealPkg
  obtain ⟨precisionUnary, endpointUnary, windowUnary, ledgerUnary, provenanceUnary,
    precisionEndpointWindow, windowLedgerProvenance, provenancePkg⟩ := carrier
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed ledgerUnary provenanceUnary ledgerProvenanceSeal
  exact
    ⟨precisionUnary, endpointUnary, windowUnary, ledgerUnary, provenanceUnary, sealUnary,
      precisionEndpointWindow, windowLedgerProvenance, ledgerProvenanceSeal, provenancePkg,
      sealPkg⟩

theorem DyadicApproximationCarrier_precision_weakening [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance weaker endpointNew windowNew ledgerNew
      provenanceNew consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      hsame precision weaker ->
        hsame endpoint endpointNew ->
          hsame ledger ledgerNew ->
            hsame provenance provenanceNew ->
              Cont weaker endpointNew windowNew ->
                Cont windowNew ledgerNew provenanceNew ->
                  Cont windowNew provenanceNew consumer ->
                    DyadicApproximationCarrier weaker endpointNew windowNew ledgerNew
                        provenanceNew bundle pkg ∧
                      UnaryHistory consumer ∧ hsame window windowNew := by
  intro carrier samePrecision sameEndpoint sameLedger sameProvenance weakerEndpointWindow
    windowLedgerProvenance consumerRow
  have transported :
      DyadicApproximationCarrier weaker endpointNew windowNew ledgerNew provenanceNew
          bundle pkg ∧
        hsame window windowNew :=
    DyadicApproximationCarrier_classifier_transport carrier samePrecision sameEndpoint
      sameLedger sameProvenance weakerEndpointWindow windowLedgerProvenance
  rcases transported with ⟨targetCarrier, sameWindow⟩
  rcases targetCarrier with
    ⟨weakerUnary, endpointUnary, windowUnary, ledgerUnary, provenanceUnary,
      weakerEndpointWindow', windowLedgerProvenance', pkgSig⟩
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed windowUnary provenanceUnary consumerRow
  exact And.intro
    ⟨weakerUnary, endpointUnary, windowUnary, ledgerUnary, provenanceUnary,
      weakerEndpointWindow', windowLedgerProvenance', pkgSig⟩
    (And.intro consumerUnary sameWindow)

theorem DyadicApproximationCarrier_window_scope [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      Cont window provenance consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory precision ∧ UnaryHistory endpoint ∧ UnaryHistory window ∧
            UnaryHistory ledger ∧ UnaryHistory provenance ∧ UnaryHistory consumer ∧
              Cont precision endpoint window ∧ Cont window ledger provenance ∧
                Cont window provenance consumer ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle consumer pkg := by
  intro carrier windowProvenanceConsumer consumerPkg
  obtain ⟨precisionUnary, endpointUnary, windowUnary, ledgerUnary, provenanceUnary,
    precisionEndpointWindow, windowLedgerProvenance, provenancePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed windowUnary provenanceUnary windowProvenanceConsumer
  exact
    ⟨precisionUnary, endpointUnary, windowUnary, ledgerUnary, provenanceUnary,
      consumerUnary, precisionEndpointWindow, windowLedgerProvenance,
      windowProvenanceConsumer, provenancePkg, consumerPkg⟩

theorem DyadicApproximationCarrier_ledger_exclusion_scope [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance consumer sealRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      Cont window provenance consumer ->
        Cont ledger provenance sealRow ->
          PkgSig bundle consumer pkg ->
            PkgSig bundle sealRow pkg ->
              SemanticNameCert
                (fun row : BHist => (hsame row consumer ∨ hsame row sealRow) ∧
                  UnaryHistory row)
                (fun row : BHist => Cont window provenance row ∨ Cont ledger provenance row)
                (fun row : BHist =>
                  PkgSig bundle row pkg ∧ UnaryHistory precision ∧ UnaryHistory endpoint ∧
                    UnaryHistory window ∧ UnaryHistory ledger ∧ UnaryHistory provenance)
                (fun row row' : BHist => hsame row row') := by
  intro carrier windowProvenanceConsumer ledgerProvenanceSeal consumerPkg sealPkg
  obtain ⟨precisionUnary, endpointUnary, windowUnary, ledgerUnary, provenanceUnary,
    _precisionEndpointWindow, _windowLedgerProvenance, _provenancePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed windowUnary provenanceUnary windowProvenanceConsumer
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed ledgerUnary provenanceUnary ledgerProvenanceSeal
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro consumer ⟨Or.inl (hsame_refl consumer), consumerUnary⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' classified
        exact hsame_symm classified
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact hsame_trans leftClassified rightClassified
      carrier_respects_equiv := by
        intro row row' classified sourceRow
        exact And.intro
          (Or.elim sourceRow.left
            (fun sameConsumer =>
              Or.inl (hsame_trans (hsame_symm classified) sameConsumer))
            (fun sameSeal =>
              Or.inr (hsame_trans (hsame_symm classified) sameSeal)))
          (unary_transport sourceRow.right classified)
    }
    pattern_sound := by
      intro row sourceRow
      exact Or.elim sourceRow.left
        (fun sameConsumer => by
          cases sameConsumer
          exact Or.inl windowProvenanceConsumer)
        (fun sameSeal => by
          cases sameSeal
          exact Or.inr ledgerProvenanceSeal)
    ledger_sound := by
      intro row sourceRow
      exact Or.elim sourceRow.left
        (fun sameConsumer => by
          cases sameConsumer
          exact
            ⟨consumerPkg, precisionUnary, endpointUnary, windowUnary, ledgerUnary,
              provenanceUnary⟩)
        (fun sameSeal => by
          cases sameSeal
          exact
            ⟨sealPkg, precisionUnary, endpointUnary, windowUnary, ledgerUnary,
              provenanceUnary⟩)
  }

theorem DyadicApproximationCarrier_terminal_window_prefix_projection [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance prefixPrecision prefixEndpoint prefixWindow
      prefixLedger prefixProvenance terminalPrecision terminalEndpoint terminalWindow
      terminalLedger terminalProvenance reread : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      hsame precision prefixPrecision ->
        hsame endpoint prefixEndpoint ->
          hsame ledger prefixLedger ->
            hsame provenance prefixProvenance ->
              Cont prefixPrecision prefixEndpoint prefixWindow ->
                Cont prefixWindow prefixLedger prefixProvenance ->
                  hsame prefixPrecision terminalPrecision ->
                    hsame prefixEndpoint terminalEndpoint ->
                      hsame prefixLedger terminalLedger ->
                        hsame prefixProvenance terminalProvenance ->
                          Cont terminalPrecision terminalEndpoint terminalWindow ->
                            Cont terminalWindow terminalLedger terminalProvenance ->
                              Cont terminalWindow terminalProvenance reread ->
                                DyadicApproximationCarrier prefixPrecision prefixEndpoint
                                    prefixWindow prefixLedger prefixProvenance bundle pkg ∧
                                  DyadicApproximationCarrier terminalPrecision terminalEndpoint
                                      terminalWindow terminalLedger terminalProvenance bundle pkg ∧
                                    UnaryHistory reread ∧ hsame prefixWindow terminalWindow := by
  intro carrier samePrecisionPrefix sameEndpointPrefix sameLedgerPrefix sameProvenancePrefix
  intro prefixPrecisionEndpointWindow prefixWindowLedgerProvenance samePrefixPrecisionTerminal
  intro samePrefixEndpointTerminal samePrefixLedgerTerminal samePrefixProvenanceTerminal
  intro terminalPrecisionEndpointWindow terminalWindowLedgerProvenance terminalWindowProvenanceReread
  have prefixTransported :
      DyadicApproximationCarrier prefixPrecision prefixEndpoint prefixWindow prefixLedger
          prefixProvenance bundle pkg ∧
        hsame window prefixWindow :=
    DyadicApproximationCarrier_classifier_transport carrier samePrecisionPrefix
      sameEndpointPrefix sameLedgerPrefix sameProvenancePrefix prefixPrecisionEndpointWindow
      prefixWindowLedgerProvenance
  have samePrecisionTerminal : hsame precision terminalPrecision :=
    hsame_trans samePrecisionPrefix samePrefixPrecisionTerminal
  have sameEndpointTerminal : hsame endpoint terminalEndpoint :=
    hsame_trans sameEndpointPrefix samePrefixEndpointTerminal
  have sameLedgerTerminal : hsame ledger terminalLedger :=
    hsame_trans sameLedgerPrefix samePrefixLedgerTerminal
  have sameProvenanceTerminal : hsame provenance terminalProvenance :=
    hsame_trans sameProvenancePrefix samePrefixProvenanceTerminal
  have terminalTransported :
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg ∧
        hsame window terminalWindow :=
    DyadicApproximationCarrier_classifier_transport carrier samePrecisionTerminal
      sameEndpointTerminal sameLedgerTerminal sameProvenanceTerminal
      terminalPrecisionEndpointWindow terminalWindowLedgerProvenance
  rcases prefixTransported with ⟨prefixCarrier, samePrefixWindow⟩
  rcases terminalTransported with ⟨terminalCarrier, sameTerminalWindow⟩
  rcases terminalCarrier with
    ⟨_terminalPrecisionUnary, _terminalEndpointUnary, terminalWindowUnary,
      _terminalLedgerUnary, terminalProvenanceUnary, terminalPrecisionEndpointWindow',
      terminalWindowLedgerProvenance', terminalPkgSig⟩
  have rereadUnary : UnaryHistory reread :=
    unary_cont_closed terminalWindowUnary terminalProvenanceUnary terminalWindowProvenanceReread
  have samePrefixTerminalWindow : hsame prefixWindow terminalWindow :=
    hsame_trans (hsame_symm samePrefixWindow) sameTerminalWindow
  exact And.intro prefixCarrier
    (And.intro
      ⟨_terminalPrecisionUnary, _terminalEndpointUnary, terminalWindowUnary,
        _terminalLedgerUnary, terminalProvenanceUnary, terminalPrecisionEndpointWindow',
        terminalWindowLedgerProvenance', terminalPkgSig⟩
      (And.intro rereadUnary samePrefixTerminalWindow))

end BEDC.Derived.DyadicApproximationUp
