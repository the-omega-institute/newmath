import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ApartnessSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ApartnessSpaceCarrier [AskSetup] [PackageSetup]
    (object located gap transport classifier zeroBoundary hroute route provenance name
      apartRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory object ∧ UnaryHistory located ∧ UnaryHistory gap ∧
    UnaryHistory transport ∧ UnaryHistory classifier ∧ UnaryHistory zeroBoundary ∧
      UnaryHistory hroute ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont located gap classifier ∧
          Cont gap classifier apartRead ∧ Cont zeroBoundary route provenance ∧
            Cont route provenance name ∧ PkgSig bundle name pkg

theorem ApartnessSpaceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {object located gap transport classifier zeroBoundary hroute route provenance name
      apartRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessSpaceCarrier object located gap transport classifier zeroBoundary hroute route
        provenance name apartRead bundle pkg ->
      SemanticNameCert
        (fun row : BHist => hsame row name ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
        (fun row : BHist => hsame row name ∧ Cont route provenance name)
        (fun row : BHist => PkgSig bundle row pkg ∧ Cont located gap classifier ∧
          Cont zeroBoundary route provenance)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier
  obtain ⟨_objectUnary, _locatedUnary, _gapUnary, _transportUnary, _classifierUnary,
    _zeroBoundaryUnary, _hrouteUnary, _routeUnary, _provenanceUnary, nameUnary,
    locatedGapClassifier, _gapClassifierApartRead, zeroBoundaryRouteProvenance,
    routeProvenanceName, namePkg⟩ :=
      carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro name ⟨hsame_refl name, nameUnary, namePkg⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, routeProvenanceName⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right.right, locatedGapClassifier, zeroBoundaryRouteProvenance⟩
  }

theorem ApartnessSpaceCarrier_located_positive_gap_route [AskSetup] [PackageSetup]
    {object located gap transport classifierExclusion zeroBoundary htransport replay provenance
      localName apartRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessSpaceCarrier object located gap transport classifierExclusion zeroBoundary
        htransport replay provenance localName apartRead bundle pkg ->
      Cont gap classifierExclusion apartRead ->
        UnaryHistory located ∧ UnaryHistory gap ∧ UnaryHistory classifierExclusion ∧
          UnaryHistory apartRead ∧ Cont located gap classifierExclusion ∧
            Cont gap classifierExclusion apartRead ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig
  intro carrier route
  cases carrier with
  | intro objectUnary rest =>
      cases rest with
      | intro locatedUnary rest =>
          cases rest with
          | intro gapUnary rest =>
              cases rest with
              | intro transportUnary rest =>
                  cases rest with
                  | intro classifierUnary rest =>
                      cases rest with
                      | intro zeroBoundaryUnary rest =>
                          cases rest with
                          | intro htransportUnary rest =>
                              cases rest with
                              | intro replayUnary rest =>
                                  cases rest with
                                  | intro provenanceUnary rest =>
                                      cases rest with
                                      | intro localNameUnary rest =>
                                          cases rest with
                                          | intro locatedGapClassifier rest =>
                                              cases rest with
                                              | intro storedRoute rest =>
                                                  cases rest with
                                                  | intro zeroBoundaryReplayProvenance rest =>
                                                      cases rest with
                                                      | intro replayProvenanceName namePkg =>
                                                          constructor
                                                          · exact locatedUnary
                                                          · constructor
                                                            · exact gapUnary
                                                            · constructor
                                                              · exact classifierUnary
                                                              · constructor
                                                                · exact
                                                                    unary_cont_closed gapUnary
                                                                      classifierUnary route
                                                                · constructor
                                                                  · exact locatedGapClassifier
                                                                  · constructor
                                                                    · exact route
                                                                    · exact namePkg

theorem ApartnessSpaceCarrier_separatedmetric_zero_distance_boundary [AskSetup] [PackageSetup]
    {object located gap transport classifierExclusion zeroBoundary htransport replay provenance
      localName apartRead zeroDistanceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessSpaceCarrier object located gap transport classifierExclusion zeroBoundary
        htransport replay provenance localName apartRead bundle pkg ->
      Cont zeroBoundary replay zeroDistanceRead ->
        PkgSig bundle zeroDistanceRead pkg ->
          UnaryHistory zeroBoundary ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
            UnaryHistory zeroDistanceRead ∧ Cont zeroBoundary replay provenance ∧
              Cont zeroBoundary replay zeroDistanceRead ∧ Cont replay provenance localName ∧
                PkgSig bundle localName pkg ∧ PkgSig bundle zeroDistanceRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle UnaryHistory
  intro carrier zeroDistanceRoute zeroDistancePkg
  cases carrier with
  | intro objectUnary rest =>
      cases rest with
      | intro locatedUnary rest =>
          cases rest with
          | intro gapUnary rest =>
              cases rest with
              | intro transportUnary rest =>
                  cases rest with
                  | intro classifierUnary rest =>
                      cases rest with
                      | intro zeroBoundaryUnary rest =>
                          cases rest with
                          | intro htransportUnary rest =>
                              cases rest with
                              | intro replayUnary rest =>
                                  cases rest with
                                  | intro provenanceUnary rest =>
                                      cases rest with
                                      | intro localNameUnary rest =>
                                          cases rest with
                                          | intro locatedGapClassifier rest =>
                                              cases rest with
                                              | intro gapClassifierApartRead rest =>
                                                  cases rest with
                                                  | intro zeroBoundaryReplayProvenance rest =>
                                                      cases rest with
                                                      | intro replayProvenanceName localNamePkg =>
                                                          constructor
                                                          · exact zeroBoundaryUnary
                                                          · constructor
                                                            · exact replayUnary
                                                            · constructor
                                                              · exact provenanceUnary
                                                              · constructor
                                                                · exact
                                                                    unary_cont_closed
                                                                      zeroBoundaryUnary
                                                                      replayUnary
                                                                      zeroDistanceRoute
                                                                · constructor
                                                                  · exact zeroBoundaryReplayProvenance
                                                                  · constructor
                                                                    · exact zeroDistanceRoute
                                                                    · constructor
                                                                      · exact replayProvenanceName
                                                                      · constructor
                                                                        · exact localNamePkg
                                                                        · exact zeroDistancePkg

theorem ApartnessSpaceClassifier_positive_gap_exactness [AskSetup] [PackageSetup]
    {object located gap transport classifierExclusion zeroBoundary htransport replay provenance
      localName apartRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessSpaceCarrier object located gap transport classifierExclusion zeroBoundary
        htransport replay provenance localName apartRead bundle pkg ->
      Cont located gap classifierExclusion ->
        Cont gap classifierExclusion apartRead ->
          PkgSig bundle localName pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row apartRead ∧ Cont gap classifierExclusion apartRead)
                (fun row : BHist =>
                  hsame row located ∨ hsame row gap ∨ hsame row classifierExclusion ∨
                    hsame row apartRead)
                (fun _row : BHist =>
                  PkgSig bundle localName pkg ∧ Cont located gap classifierExclusion ∧
                    Cont gap classifierExclusion apartRead)
                hsame ∧
              UnaryHistory located ∧ UnaryHistory gap ∧ UnaryHistory classifierExclusion := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier locatedGapClassifier gapClassifierApartRead localNamePkg
  obtain ⟨_objectUnary, locatedUnary, gapUnary, _transportUnary, classifierUnary,
    _zeroBoundaryUnary, _htransportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _storedLocatedGapClassifier, _storedGapClassifierApartRead, _zeroBoundaryReplayProvenance,
    _replayProvenanceName, _storedNamePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row apartRead ∧ Cont gap classifierExclusion apartRead)
          (fun row : BHist =>
            hsame row located ∨ hsame row gap ∨ hsame row classifierExclusion ∨
              hsame row apartRead)
          (fun _row : BHist =>
            PkgSig bundle localName pkg ∧ Cont located gap classifierExclusion ∧
              Cont gap classifierExclusion apartRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro apartRead ⟨hsame_refl apartRead, gapClassifierApartRead⟩
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
            ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr sourceRow.left))
      ledger_sound := by
        intro _row _sourceRow
        exact ⟨localNamePkg, locatedGapClassifier, gapClassifierApartRead⟩
    }
  exact ⟨cert, locatedUnary, gapUnary, classifierUnary⟩

theorem ApartnessSpaceCarrier_positive_gap_transport [AskSetup] [PackageSetup]
    {object located gap transport classifierExclusion zeroBoundary htransport replay provenance
      localName apartRead located' gap' classifierExclusion' apartRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessSpaceCarrier object located gap transport classifierExclusion zeroBoundary
        htransport replay provenance localName apartRead bundle pkg ->
      hsame located located' ->
        hsame gap gap' ->
          hsame classifierExclusion classifierExclusion' ->
            hsame apartRead apartRead' ->
              Cont located' gap' classifierExclusion' ∧
                Cont gap' classifierExclusion' apartRead' ∧
                  UnaryHistory located' ∧ UnaryHistory gap' ∧
                    UnaryHistory classifierExclusion' ∧ UnaryHistory apartRead' := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier locatedSame gapSame classifierSame apartReadSame
  obtain ⟨_objectUnary, locatedUnary, gapUnary, _transportUnary, classifierUnary,
    _zeroBoundaryUnary, _htransportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    locatedGapClassifier, gapClassifierApartRead, _zeroBoundaryReplayProvenance,
    _replayProvenanceName, _localNamePkg⟩ := carrier
  have apartReadUnary : UnaryHistory apartRead :=
    unary_cont_closed gapUnary classifierUnary gapClassifierApartRead
  cases locatedSame
  cases gapSame
  cases classifierSame
  cases apartReadSame
  exact
    ⟨locatedGapClassifier, gapClassifierApartRead, locatedUnary, gapUnary, classifierUnary,
      apartReadUnary⟩

end BEDC.Derived.ApartnessSpaceUp
