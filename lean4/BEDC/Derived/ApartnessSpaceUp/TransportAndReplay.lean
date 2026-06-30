import BEDC.Derived.ApartnessSpaceUp

namespace BEDC.Derived.ApartnessSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApartnessSpaceCarrier_transport_and_replay [AskSetup] [PackageSetup]
    {object located gap transport classifierExclusion zeroBoundary htransport replay provenance
      localName apartRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessSpaceCarrier object located gap transport classifierExclusion zeroBoundary
        htransport replay provenance localName apartRead bundle pkg ->
      Cont htransport replay replayRead ->
        PkgSig bundle replayRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row object ∨ hsame row located ∨ hsame row gap ∨
                  hsame row classifierExclusion ∨ hsame row zeroBoundary ∨
                    hsame row htransport ∨ hsame row replay ∨ hsame row provenance ∨
                      hsame row localName ∨ hsame row replayRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont located gap classifierExclusion ∧
                  Cont gap classifierExclusion apartRead ∧ Cont htransport replay replayRead ∧
                    PkgSig bundle replayRead pkg)
              hsame ∧
            UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier replayRoute replayPkg
  obtain ⟨_objectUnary, _locatedUnary, _gapUnary, _transportUnary, _classifierUnary,
    _zeroBoundaryUnary, htransportUnary, replayUnary, _provenanceUnary, _localNameUnary,
    locatedGapClassifier, gapClassifierApartRead, _zeroBoundaryReplayProvenance,
    _replayProvenanceName, _localNamePkg⟩ := carrier
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed htransportUnary replayUnary replayRoute
  have sourceReplay :
      (fun row : BHist => hsame row replayRead ∧ UnaryHistory row) replayRead := by
    exact ⟨hsame_refl replayRead, replayReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row object ∨ hsame row located ∨ hsame row gap ∨
              hsame row classifierExclusion ∨ hsame row zeroBoundary ∨
                hsame row htransport ∨ hsame row replay ∨ hsame row provenance ∨
                  hsame row localName ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont located gap classifierExclusion ∧
              Cont gap classifierExclusion apartRead ∧ Cont htransport replay replayRead ∧
                PkgSig bundle replayRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead sourceReplay
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr sourceRow.left))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, locatedGapClassifier, gapClassifierApartRead, replayRoute,
          replayPkg⟩
  }
  exact ⟨cert, replayReadUnary⟩

theorem ApartnessSpaceCarrier_package_transport_replay_boundary [AskSetup] [PackageSetup]
    {object located gap transport classifierExclusion zeroBoundary htransport replay provenance
      localName apartRead zeroDistanceRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessSpaceCarrier object located gap transport classifierExclusion zeroBoundary
        htransport replay provenance localName apartRead bundle pkg ->
      Cont gap classifierExclusion apartRead ->
        Cont zeroBoundary replay zeroDistanceRead ->
          Cont htransport replay replayRead ->
            PkgSig bundle localName pkg ->
              PkgSig bundle zeroDistanceRead pkg ->
                PkgSig bundle replayRead pkg ->
                  (SemanticNameCert
                        (fun row : BHist => hsame row localName ∧ PkgSig bundle localName pkg)
                        (fun row : BHist =>
                          hsame row object ∨ hsame row located ∨ hsame row gap ∨
                            hsame row classifierExclusion ∨ hsame row zeroBoundary ∨
                              hsame row localName)
                        (fun _row : BHist =>
                          PkgSig bundle localName pkg ∧ Cont gap classifierExclusion apartRead ∧
                            Cont zeroBoundary replay zeroDistanceRead)
                        hsame ∧
                      SemanticNameCert
                        (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row object ∨ hsame row located ∨ hsame row gap ∨
                            hsame row classifierExclusion ∨ hsame row zeroBoundary ∨
                              hsame row htransport ∨ hsame row replay ∨ hsame row provenance ∨
                                hsame row localName ∨ hsame row replayRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont located gap classifierExclusion ∧
                            Cont gap classifierExclusion apartRead ∧
                              Cont htransport replay replayRead ∧ PkgSig bundle replayRead pkg)
                        hsame) ∧
                    UnaryHistory located ∧ UnaryHistory gap ∧
                      UnaryHistory classifierExclusion ∧ UnaryHistory zeroBoundary ∧
                        UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier positiveGapRoute zeroDistanceRoute replayRoute localNamePkg zeroDistancePkg
    replayPkg
  have localPackage :=
    ApartnessSpaceCarrier_namecert_obligation_package (bundle := bundle) (pkg := pkg)
      carrier positiveGapRoute zeroDistanceRoute localNamePkg zeroDistancePkg
  have replayPackage :=
    ApartnessSpaceCarrier_transport_and_replay (bundle := bundle) (pkg := pkg)
      carrier replayRoute replayPkg
  obtain ⟨localCert, locatedUnary, gapUnary, classifierUnary, zeroBoundaryUnary⟩ :=
    localPackage
  obtain ⟨replayCert, replayReadUnary⟩ := replayPackage
  exact
    ⟨⟨localCert, replayCert⟩, locatedUnary, gapUnary, classifierUnary, zeroBoundaryUnary,
      replayReadUnary⟩

end BEDC.Derived.ApartnessSpaceUp
