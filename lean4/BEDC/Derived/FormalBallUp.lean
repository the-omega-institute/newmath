import BEDC.Derived.FormalBallCompletionUp.TasteGate
import BEDC.Derived.FormalBallUp.CenterRadiusAdmission
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FormalBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FormalBallCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {metric radius dyadic window transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FormalBallCarrier metric radius dyadic window transport replay provenance localName
        bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row localName ∧
              FormalBallCarrier metric radius dyadic window transport replay provenance
                localName bundle pkg)
          (fun row : BHist =>
            hsame row localName ∧ Cont metric radius dyadic ∧ Cont dyadic window replay)
          (fun row : BHist => hsame row localName ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory metric ∧ UnaryHistory radius ∧ UnaryHistory dyadic ∧
          UnaryHistory window ∧ Cont metric radius dyadic ∧ Cont dyadic window replay ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier
  have carrierSource :
      FormalBallCarrier metric radius dyadic window transport replay provenance localName
        bundle pkg := carrier
  obtain ⟨metricUnary, radiusUnary, dyadicUnary, windowUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, metricRadiusDyadic,
    dyadicWindowReplay, _transportReplayProvenance, provenancePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row localName ∧
              FormalBallCarrier metric radius dyadic window transport replay provenance
                localName bundle pkg)
          (fun row : BHist =>
            hsame row localName ∧ Cont metric radius dyadic ∧ Cont dyadic window replay)
          (fun row : BHist => hsame row localName ∧ PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro localName
          ⟨hsame_refl localName, carrierSource⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows source
          exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, metricRadiusDyadic, dyadicWindowReplay⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, provenancePkg⟩
    }
  exact
    ⟨cert, metricUnary, radiusUnary, dyadicUnary, windowUnary, metricRadiusDyadic,
      dyadicWindowReplay, provenancePkg⟩

theorem FormalBallRadiusRefinement [AskSetup] [PackageSetup]
    {M R D W H C P N refinedWindow : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    FormalBallCarrier M R D W H C P N bundle pkg ->
      Cont R D refinedWindow ->
        PkgSig bundle refinedWindow pkg ->
          UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory W ∧
            UnaryHistory refinedWindow ∧ PkgSig bundle P pkg ∧
              PkgSig bundle refinedWindow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier radiusDyadicRefinement refinedPkg
  obtain ⟨metricUnary, radiusUnary, dyadicUnary, windowUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _nameCertUnary, _metricRadius, _dyadicWindow,
    _transportReplay, provenancePkg⟩ := carrier
  have refinedUnary : UnaryHistory refinedWindow :=
    unary_cont_closed radiusUnary dyadicUnary radiusDyadicRefinement
  exact
    ⟨metricUnary, radiusUnary, dyadicUnary, windowUnary, refinedUnary, provenancePkg,
      refinedPkg⟩

theorem FormalBallCarrier_directed_radius_transport [AskSetup] [PackageSetup]
    {M R D W H C P N radiusRead transportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FormalBallCarrier M R D W H C P N bundle pkg ->
      Cont R D radiusRead ->
        Cont radiusRead C transportedRead ->
          PkgSig bundle transportedRead pkg ->
            UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory C ∧
              UnaryHistory radiusRead ∧ UnaryHistory transportedRead ∧
                Cont R D radiusRead ∧ Cont radiusRead C transportedRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle transportedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier radiusRoute transportedRoute transportedPkg
  obtain ⟨_metricUnary, radiusUnary, dyadicUnary, _windowUnary, _transportUnary,
    replayUnary, _provenanceUnary, _nameCertUnary, _metricRadius, _dyadicWindow,
    _transportReplay, provenancePkg⟩ := carrier
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiusUnary dyadicUnary radiusRoute
  have transportedReadUnary : UnaryHistory transportedRead :=
    unary_cont_closed radiusReadUnary replayUnary transportedRoute
  exact
    ⟨radiusUnary, dyadicUnary, replayUnary, radiusReadUnary, transportedReadUnary,
      radiusRoute, transportedRoute, provenancePkg, transportedPkg⟩

theorem FormalBallCarrier_completion_window_handoff [AskSetup] [PackageSetup]
    {M R D W H C P N completionRead exportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FormalBallCarrier M R D W H C P N bundle pkg ->
      Cont M R D ->
        Cont D W completionRead ->
          Cont completionRead C exportedRead ->
            PkgSig bundle exportedRead pkg ->
              UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory W ∧
                UnaryHistory completionRead ∧ UnaryHistory exportedRead ∧ Cont M R D ∧
                  Cont D W completionRead ∧ Cont completionRead C exportedRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle exportedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier metricRadiusDyadic dyadicWindowCompletion completionExport exportedPkg
  obtain ⟨metricUnary, radiusUnary, dyadicUnary, windowUnary, _transportUnary,
    replayUnary, _provenanceUnary, _nameCertUnary, _metricRadius, _dyadicWindowReplay,
    _transportReplay, provenancePkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed dyadicUnary windowUnary dyadicWindowCompletion
  have exportedUnary : UnaryHistory exportedRead :=
    unary_cont_closed completionUnary replayUnary completionExport
  exact
    ⟨metricUnary, radiusUnary, dyadicUnary, windowUnary, completionUnary, exportedUnary,
      metricRadiusDyadic, dyadicWindowCompletion, completionExport, provenancePkg, exportedPkg⟩

theorem FormalBallCarrier_cauchy_filter_handoff [AskSetup] [PackageSetup]
    {M R D W H C P N completionRead cauchyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FormalBallCarrier M R D W H C P N bundle pkg ->
      Cont D W completionRead ->
        Cont completionRead C cauchyRead ->
          PkgSig bundle cauchyRead pkg ->
            UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory W ∧
              UnaryHistory completionRead ∧ UnaryHistory cauchyRead ∧
                Cont D W completionRead ∧ Cont completionRead C cauchyRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle cauchyRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier completionRoute cauchyRoute cauchyPkg
  obtain ⟨metricUnary, radiusUnary, dyadicUnary, windowUnary, _transportUnary,
    replayUnary, _provenanceUnary, _nameCertUnary, _metricRadius, _dyadicWindowReplay,
    _transportReplay, provenancePkg⟩ := carrier
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed dyadicUnary windowUnary completionRoute
  have cauchyReadUnary : UnaryHistory cauchyRead :=
    unary_cont_closed completionReadUnary replayUnary cauchyRoute
  exact
    ⟨metricUnary, radiusUnary, dyadicUnary, windowUnary, completionReadUnary,
      cauchyReadUnary, completionRoute, cauchyRoute, provenancePkg, cauchyPkg⟩

theorem FormalBallCarrier_radius_refinement_chain [AskSetup] [PackageSetup]
    {M R D W H C P N firstRefined finalRefined : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FormalBallCarrier M R D W H C P N bundle pkg ->
      Cont R D firstRefined ->
        Cont firstRefined D finalRefined ->
          PkgSig bundle finalRefined pkg ->
            UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory firstRefined ∧
              UnaryHistory finalRefined ∧ Cont R D firstRefined ∧
                Cont firstRefined D finalRefined ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle finalRefined pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier firstRoute finalRoute finalPkg
  obtain ⟨_metricUnary, radiusUnary, dyadicUnary, _windowUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _nameCertUnary, _metricRadius, _dyadicWindowReplay,
    _transportReplay, provenancePkg⟩ := carrier
  have firstUnary : UnaryHistory firstRefined :=
    unary_cont_closed radiusUnary dyadicUnary firstRoute
  have finalUnary : UnaryHistory finalRefined :=
    unary_cont_closed firstUnary dyadicUnary finalRoute
  exact
    ⟨radiusUnary, dyadicUnary, firstUnary, finalUnary, firstRoute, finalRoute,
      provenancePkg, finalPkg⟩

end BEDC.Derived.FormalBallUp
