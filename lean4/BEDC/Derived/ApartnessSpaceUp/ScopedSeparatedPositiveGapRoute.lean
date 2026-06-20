import BEDC.Derived.ApartnessSpaceUp

namespace BEDC.Derived.ApartnessSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApartnessSpaceCarrier_scoped_separated_positive_gap_route [AskSetup] [PackageSetup]
    {object located gap transport classifierExclusion zeroBoundary htransport replay provenance
      localName apartRead zeroDistanceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessSpaceCarrier object located gap transport classifierExclusion zeroBoundary
        htransport replay provenance localName apartRead bundle pkg →
      Cont gap classifierExclusion apartRead →
        Cont zeroBoundary replay zeroDistanceRead →
          PkgSig bundle zeroDistanceRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row apartRead ∧ Cont gap classifierExclusion apartRead)
                (fun row : BHist =>
                  hsame row located ∨ hsame row gap ∨ hsame row classifierExclusion ∨
                    hsame row apartRead ∨ hsame row zeroBoundary ∨ hsame row zeroDistanceRead)
                (fun _row : BHist =>
                  PkgSig bundle localName pkg ∧ Cont located gap classifierExclusion ∧
                    Cont gap classifierExclusion apartRead ∧
                      Cont zeroBoundary replay zeroDistanceRead ∧
                        PkgSig bundle zeroDistanceRead pkg)
                hsame ∧
              UnaryHistory located ∧ UnaryHistory gap ∧ UnaryHistory classifierExclusion ∧
                UnaryHistory zeroBoundary ∧ UnaryHistory replay ∧
                  UnaryHistory zeroDistanceRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier positiveGapRoute zeroDistanceRoute zeroDistancePkg
  obtain ⟨_objectUnary, locatedUnary, gapUnary, _transportUnary, classifierUnary,
    zeroBoundaryUnary, _htransportUnary, replayUnary, _provenanceUnary, _localNameUnary,
    locatedGapClassifier, _storedPositiveGapRoute, _zeroBoundaryReplayProvenance,
    _replayProvenanceName, localNamePkg⟩ := carrier
  have zeroDistanceUnary : UnaryHistory zeroDistanceRead :=
    unary_cont_closed zeroBoundaryUnary replayUnary zeroDistanceRoute
  have sourceApart :
      (fun row : BHist => hsame row apartRead ∧ Cont gap classifierExclusion apartRead)
          apartRead := by
    exact ⟨hsame_refl apartRead, positiveGapRoute⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row apartRead ∧ Cont gap classifierExclusion apartRead)
          (fun row : BHist =>
            hsame row located ∨ hsame row gap ∨ hsame row classifierExclusion ∨
              hsame row apartRead ∨ hsame row zeroBoundary ∨ hsame row zeroDistanceRead)
          (fun _row : BHist =>
            PkgSig bundle localName pkg ∧ Cont located gap classifierExclusion ∧
              Cont gap classifierExclusion apartRead ∧ Cont zeroBoundary replay zeroDistanceRead ∧
                PkgSig bundle zeroDistanceRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro apartRead sourceApart
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
      exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
    ledger_sound := by
      intro _row _source
      exact
        ⟨localNamePkg, locatedGapClassifier, positiveGapRoute, zeroDistanceRoute,
          zeroDistancePkg⟩
  }
  exact
    ⟨cert, locatedUnary, gapUnary, classifierUnary, zeroBoundaryUnary, replayUnary,
      zeroDistanceUnary⟩

end BEDC.Derived.ApartnessSpaceUp
