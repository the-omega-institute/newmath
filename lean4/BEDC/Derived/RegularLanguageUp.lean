import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularLanguageUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularLanguageAutomatonPacket [AskSetup] [PackageSetup]
    (alphabet states start accept transition word run endpoint transport routes provenance :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory alphabet ∧ UnaryHistory states ∧ UnaryHistory start ∧ UnaryHistory accept ∧
    UnaryHistory transition ∧ UnaryHistory word ∧ UnaryHistory run ∧
      UnaryHistory endpoint ∧ UnaryHistory transport ∧ UnaryHistory routes ∧
        UnaryHistory provenance ∧ Cont start word run ∧ Cont run transition endpoint ∧
          Cont endpoint transport routes ∧ PkgSig bundle provenance pkg

def RegularLanguageAutomatonClassifier [AskSetup] [PackageSetup]
    (alphabet states start accept transition word run endpoint transport routes provenance
      alphabet' states' start' accept' transition' word' run' endpoint' transport' routes'
      provenance' : BHist) : Prop :=
  hsame alphabet alphabet' ∧ hsame states states' ∧ hsame start start' ∧
    hsame accept accept' ∧ hsame transition transition' ∧ hsame word word' ∧
      hsame run run' ∧ hsame endpoint endpoint' ∧ hsame transport transport' ∧
        hsame routes routes' ∧ hsame provenance provenance'

theorem RegularLanguageAutomatonPacket_run_ledger_deterministic [AskSetup] [PackageSetup]
    {alphabet states start accept transition word run endpoint transport routes provenance run'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularLanguageAutomatonPacket alphabet states start accept transition word run endpoint
        transport routes provenance bundle pkg ->
      Cont start word run' -> Cont run' transition endpoint' ->
        hsame run run' ∧ hsame endpoint endpoint' := by
  intro packet runRow' endpointRow'
  obtain ⟨_alphabetUnary, _statesUnary, _startUnary, _acceptUnary, _transitionUnary,
    _wordUnary, _runUnary, _endpointUnary, _transportUnary, _routesUnary, _provenanceUnary,
    runRow, endpointRow, _routesRow, _pkgSig⟩ := packet
  have sameRun : hsame run run' :=
    cont_deterministic runRow runRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameRun (hsame_refl transition) endpointRow endpointRow'
  exact ⟨sameRun, sameEndpoint⟩

theorem RegularLanguageAutomatonPacket_deterministic_run_ledger [AskSetup] [PackageSetup]
    {alphabet states start accept transition word run endpoint transport routes provenance
      run' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularLanguageAutomatonPacket alphabet states start accept transition word run endpoint
        transport routes provenance bundle pkg ->
      Cont start word run' ->
        UnaryHistory start ∧ UnaryHistory word ∧ UnaryHistory run' ∧ hsame run run' ∧
          Cont start word run' ∧ PkgSig bundle provenance pkg := by
  intro packet runRow'
  obtain ⟨_alphabetUnary, _statesUnary, startUnary, _acceptUnary, _transitionUnary,
    wordUnary, _runUnary, _endpointUnary, _transportUnary, _routesUnary, _provenanceUnary,
    runRow, _endpointRow, _routesRow, pkgSig⟩ := packet
  have sameRun : hsame run run' :=
    cont_deterministic runRow runRow'
  have runUnary' : UnaryHistory run' :=
    unary_cont_closed startUnary wordUnary runRow'
  exact
    ⟨startUnary, wordUnary, runUnary', sameRun, runRow', pkgSig⟩

theorem RegularLanguageAutomatonPacket_run_prefix_restriction [AskSetup] [PackageSetup]
    {alphabet states start accept transition word run endpoint transport routes provenance pref
      prefRun prefEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularLanguageAutomatonPacket alphabet states start accept transition word run endpoint
        transport routes provenance bundle pkg ->
      hsame word pref ->
        Cont start pref prefRun ->
          Cont prefRun transition prefEndpoint ->
            UnaryHistory pref ∧ UnaryHistory prefRun ∧ UnaryHistory prefEndpoint ∧
              hsame run prefRun ∧ hsame endpoint prefEndpoint ∧
                PkgSig bundle provenance pkg := by
  intro packet sameWord prefRunRow prefEndpointRow
  obtain ⟨_alphabetUnary, _statesUnary, startUnary, _acceptUnary, transitionUnary,
    wordUnary, _runUnary, _endpointUnary, _transportUnary, _routesUnary, _provenanceUnary,
    runRow, endpointRow, _routesRow, pkgSig⟩ := packet
  have prefUnary : UnaryHistory pref :=
    unary_transport wordUnary sameWord
  have prefRunUnary : UnaryHistory prefRun :=
    unary_cont_closed startUnary prefUnary prefRunRow
  have prefEndpointUnary : UnaryHistory prefEndpoint :=
    unary_cont_closed prefRunUnary transitionUnary prefEndpointRow
  have sameRun : hsame run prefRun :=
    cont_respects_hsame (hsame_refl start) sameWord runRow prefRunRow
  have sameEndpoint : hsame endpoint prefEndpoint :=
    cont_respects_hsame sameRun (hsame_refl transition) endpointRow prefEndpointRow
  exact
    ⟨prefUnary, prefRunUnary, prefEndpointUnary, sameRun, sameEndpoint, pkgSig⟩

theorem RegularLanguageAutomatonPacket_classified_word_transport [AskSetup] [PackageSetup]
    {alphabet states start accept transition word run endpoint transport routes provenance run'
      transition' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularLanguageAutomatonPacket alphabet states start accept transition word run endpoint
        transport routes provenance bundle pkg ->
      hsame run run' ->
        hsame transition transition' ->
          Cont run' transition' endpoint' ->
            UnaryHistory run' ∧ UnaryHistory transition' ∧ UnaryHistory endpoint' ∧
              hsame endpoint endpoint' ∧ Cont run' transition' endpoint' ∧
                PkgSig bundle provenance pkg := by
  intro packet sameRun sameTransition endpointRow'
  obtain ⟨_alphabetUnary, _statesUnary, startUnary, _acceptUnary, transitionUnary,
    wordUnary, _runUnary, _endpointUnary, _transportUnary, _routesUnary, _provenanceUnary,
    runRow, endpointRow, _routesRow, pkgSig⟩ := packet
  have runUnary : UnaryHistory run :=
    unary_cont_closed startUnary wordUnary runRow
  have runUnary' : UnaryHistory run' :=
    unary_transport runUnary sameRun
  have transitionUnary' : UnaryHistory transition' :=
    unary_transport transitionUnary sameTransition
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed runUnary' transitionUnary' endpointRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameRun sameTransition endpointRow endpointRow'
  exact
    ⟨runUnary', transitionUnary', endpointUnary', sameEndpoint, endpointRow', pkgSig⟩

theorem RegularLanguageAutomatonPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {alphabet states start accept transition word run endpoint transport routes provenance run'
      endpoint' publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularLanguageAutomatonPacket alphabet states start accept transition word run endpoint
        transport routes provenance bundle pkg ->
      Cont start word run' ->
        Cont run' transition endpoint' ->
          Cont endpoint' transport publicRead ->
            PkgSig bundle publicRead pkg ->
              UnaryHistory alphabet ∧ UnaryHistory states ∧ UnaryHistory start ∧
                UnaryHistory accept ∧ UnaryHistory transition ∧ UnaryHistory word ∧
                  UnaryHistory run' ∧ UnaryHistory endpoint' ∧ UnaryHistory publicRead ∧
                    hsame run run' ∧ hsame endpoint endpoint' ∧
                      Cont endpoint' transport publicRead ∧ PkgSig bundle publicRead pkg := by
  intro packet runRow' endpointRow' publicReadRow publicReadPkg
  obtain ⟨alphabetUnary, statesUnary, startUnary, acceptUnary, transitionUnary, wordUnary,
    runUnary, endpointUnary, transportUnary, _routesUnary, _provenanceUnary, runRow,
    endpointRow, _routesRow, _pkgSig⟩ := packet
  have sameRun : hsame run run' :=
    cont_deterministic runRow runRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameRun (hsame_refl transition) endpointRow endpointRow'
  have runUnary' : UnaryHistory run' :=
    unary_cont_closed startUnary wordUnary runRow'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed runUnary' transitionUnary endpointRow'
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed endpointUnary' transportUnary publicReadRow
  exact
    ⟨alphabetUnary, statesUnary, startUnary, acceptUnary, transitionUnary, wordUnary,
      runUnary', endpointUnary', publicReadUnary, sameRun, sameEndpoint, publicReadRow,
      publicReadPkg⟩

theorem RegularLanguageAutomatonPacket_public_accepted_word_export [AskSetup] [PackageSetup]
    {alphabet states start accept transition word run endpoint transport routes provenance
      publicExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularLanguageAutomatonPacket alphabet states start accept transition word run endpoint
        transport routes provenance bundle pkg ->
      Cont routes provenance publicExport ->
        PkgSig bundle publicExport pkg ->
          UnaryHistory alphabet ∧ UnaryHistory states ∧ UnaryHistory start ∧
            UnaryHistory accept ∧ UnaryHistory transition ∧ UnaryHistory word ∧
              UnaryHistory run ∧ UnaryHistory endpoint ∧ UnaryHistory transport ∧
                UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory publicExport ∧
                  Cont start word run ∧ Cont run transition endpoint ∧
                    Cont endpoint transport routes ∧ Cont routes provenance publicExport ∧
                      PkgSig bundle publicExport pkg := by
  intro packet exportRow publicSig
  obtain ⟨alphabetUnary, statesUnary, startUnary, acceptUnary, transitionUnary, wordUnary,
    runUnary, endpointUnary, transportUnary, routesUnary, provenanceUnary, runRow,
    endpointRow, routesRow, _pkgSig⟩ := packet
  have publicUnary : UnaryHistory publicExport :=
    unary_cont_closed routesUnary provenanceUnary exportRow
  exact
    ⟨alphabetUnary, statesUnary, startUnary, acceptUnary, transitionUnary, wordUnary,
      runUnary, endpointUnary, transportUnary, routesUnary, provenanceUnary, publicUnary,
        runRow, endpointRow, routesRow, exportRow, publicSig⟩

theorem RegularLanguageAutomatonPacket_standard_automaton_bridge_boundary [AskSetup]
    [PackageSetup]
    {alphabet states start accept transition word run endpoint transport routes provenance
      boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularLanguageAutomatonPacket alphabet states start accept transition word run endpoint
        transport routes provenance bundle pkg ->
      Cont routes accept boundary ->
        PkgSig bundle boundary pkg ->
          UnaryHistory alphabet ∧ UnaryHistory states ∧ UnaryHistory start ∧
            UnaryHistory accept ∧ UnaryHistory transition ∧ UnaryHistory word ∧
              UnaryHistory run ∧ UnaryHistory endpoint ∧ UnaryHistory transport ∧
                UnaryHistory routes ∧ UnaryHistory boundary ∧ Cont start word run ∧
                  Cont run transition endpoint ∧ Cont endpoint transport routes ∧
                    Cont routes accept boundary ∧ PkgSig bundle boundary pkg := by
  intro packet routesAcceptBoundary boundaryPkg
  obtain ⟨alphabetUnary, statesUnary, startUnary, acceptUnary, transitionUnary, wordUnary,
    runUnary, endpointUnary, transportUnary, routesUnary, _provenanceUnary, runRow,
    endpointRow, routesRow, _provenancePkg⟩ := packet
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed routesUnary acceptUnary routesAcceptBoundary
  exact
    ⟨alphabetUnary, statesUnary, startUnary, acceptUnary, transitionUnary, wordUnary,
      runUnary, endpointUnary, transportUnary, routesUnary, boundaryUnary, runRow,
      endpointRow, routesRow, routesAcceptBoundary, boundaryPkg⟩

theorem RegularLanguageAutomatonPacket_transition_ledger_standard_boundary [AskSetup]
    [PackageSetup]
    {alphabet states start accept transition word run endpoint transport routes provenance
      boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularLanguageAutomatonPacket alphabet states start accept transition word run endpoint
        transport routes provenance bundle pkg ->
      Cont routes provenance boundary ->
        PkgSig bundle boundary pkg ->
          UnaryHistory run ∧ UnaryHistory endpoint ∧ UnaryHistory routes ∧
            UnaryHistory provenance ∧ UnaryHistory boundary ∧ Cont start word run ∧
              Cont run transition endpoint ∧ Cont endpoint transport routes ∧
                Cont routes provenance boundary ∧ PkgSig bundle boundary pkg := by
  intro packet boundaryRow boundarySig
  obtain ⟨_alphabetUnary, _statesUnary, _startUnary, _acceptUnary, _transitionUnary,
    _wordUnary, runUnary, endpointUnary, _transportUnary, routesUnary, provenanceUnary,
    runRow, endpointRow, routesRow, _pkgSig⟩ := packet
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed routesUnary provenanceUnary boundaryRow
  exact
    ⟨runUnary, endpointUnary, routesUnary, provenanceUnary, boundaryUnary, runRow, endpointRow,
      routesRow, boundaryRow, boundarySig⟩

theorem RegularLanguageAutomatonPacket_scoped_dependency_reassociation_witness
    [AskSetup] [PackageSetup]
    {alphabet states start accept transition word run endpoint transport routes provenance read
      folded scopedRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularLanguageAutomatonPacket alphabet states start accept transition word run endpoint
        transport routes provenance bundle pkg ->
      UnaryHistory read ->
        Cont endpoint read folded ->
          Cont folded provenance scopedRow ->
            exists tail : BHist, exists scoped' : BHist,
              Cont read provenance tail ∧ Cont endpoint tail scoped' ∧
                hsame scopedRow scoped' ∧ UnaryHistory tail ∧ UnaryHistory scoped' := by
  intro packet readUnary endpointReadRow foldedProvenanceRow
  obtain ⟨_alphabetUnary, _statesUnary, _startUnary, _acceptUnary, _transitionUnary,
    _wordUnary, _runUnary, endpointUnary, _transportUnary, _routesUnary, provenanceUnary,
    _runRow, _endpointRow, _routesRow, _pkgSig⟩ := packet
  cases cont_assoc_left_exists endpointReadRow foldedProvenanceRow with
  | intro tail reassociated =>
      have tailUnary : UnaryHistory tail :=
        unary_cont_closed readUnary provenanceUnary reassociated.left
      have scopedUnary : UnaryHistory scopedRow :=
        unary_cont_closed
          (unary_cont_closed endpointUnary readUnary endpointReadRow) provenanceUnary
          foldedProvenanceRow
      exact
        ⟨tail, scopedRow, reassociated.left, reassociated.right, hsame_refl scopedRow,
          tailUnary, scopedUnary⟩

theorem RegularLanguageAutomatonPacket_finite_bridge_consumer_completeness
    [AskSetup] [PackageSetup]
    {alphabet states start accept transition word run endpoint transport routes provenance
      publicExport bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularLanguageAutomatonPacket alphabet states start accept transition word run endpoint
        transport routes provenance bundle pkg ->
      Cont routes provenance publicExport ->
        Cont publicExport transport bridgeRead ->
          PkgSig bundle publicExport pkg ->
            PkgSig bundle bridgeRead pkg ->
              UnaryHistory alphabet ∧ UnaryHistory states ∧ UnaryHistory start ∧
                UnaryHistory accept ∧ UnaryHistory transition ∧ UnaryHistory word ∧
                  UnaryHistory run ∧ UnaryHistory endpoint ∧ UnaryHistory publicExport ∧
                    UnaryHistory bridgeRead ∧ Cont routes provenance publicExport ∧
                      Cont publicExport transport bridgeRead ∧ PkgSig bundle bridgeRead pkg := by
  intro packet publicRow bridgeRow _publicSig bridgeSig
  obtain ⟨alphabetUnary, statesUnary, startUnary, acceptUnary, transitionUnary, wordUnary,
    runUnary, endpointUnary, transportUnary, routesUnary, provenanceUnary, _runRow,
    _endpointRow, _routesRow, _pkgSig⟩ := packet
  have publicUnary : UnaryHistory publicExport :=
    unary_cont_closed routesUnary provenanceUnary publicRow
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed publicUnary transportUnary bridgeRow
  exact
    ⟨alphabetUnary, statesUnary, startUnary, acceptUnary, transitionUnary, wordUnary,
      runUnary, endpointUnary, publicUnary, bridgeUnary, publicRow, bridgeRow, bridgeSig⟩

theorem RegularLanguageAutomatonPacket_scoped_kernel_dependency_envelope
    [AskSetup] [PackageSetup]
    {alphabet states start accept transition word run endpoint transport routes provenance
      envelope : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularLanguageAutomatonPacket alphabet states start accept transition word run endpoint
        transport routes provenance bundle pkg ->
      Cont provenance routes envelope ->
        PkgSig bundle envelope pkg ->
          SemanticNameCert
            (fun row : BHist => hsame row envelope ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
            (fun row : BHist => UnaryHistory row ∧ Cont provenance routes row)
            (fun row : BHist => PkgSig bundle row pkg ∧ UnaryHistory provenance ∧
              UnaryHistory routes)
            (fun row row' : BHist => hsame row row') := by
  intro packet envelopeRow envelopeSig
  obtain ⟨_alphabetUnary, _statesUnary, _startUnary, _acceptUnary, _transitionUnary,
    _wordUnary, _runUnary, _endpointUnary, _transportUnary, routesUnary, provenanceUnary,
    _runRow, _endpointRow, _routesRow, _pkgSig⟩ := packet
  have envelopeUnary : UnaryHistory envelope :=
    unary_cont_closed provenanceUnary routesUnary envelopeRow
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro envelope ⟨hsame_refl envelope, envelopeUnary, envelopeSig⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRow
        exact hsame_symm sameRow
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      obtain ⟨sameEnvelope, rowUnary, _rowSig⟩ := sourceRow
      cases sameEnvelope
      exact ⟨rowUnary, envelopeRow⟩
    ledger_sound := by
      intro _row sourceRow
      obtain ⟨_sameEnvelope, _rowUnary, rowSig⟩ := sourceRow
      exact ⟨rowSig, provenanceUnary, routesUnary⟩
  }

end BEDC.Derived.RegularLanguageUp
