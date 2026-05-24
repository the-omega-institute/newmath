import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FilterBaseUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FilterBaseCarrier [AskSetup] [PackageSetup]
    (index baseElement directed refinement transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory index ∧ UnaryHistory baseElement ∧ UnaryHistory refinement ∧
    UnaryHistory transport ∧ UnaryHistory localName ∧ Cont index baseElement directed ∧
      Cont directed refinement replay ∧ Cont transport replay provenance ∧
        PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem FilterBaseCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {index baseElement directed refinement transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FilterBaseCarrier index baseElement directed refinement transport replay provenance
        localName bundle pkg →
      UnaryHistory index ∧ UnaryHistory baseElement ∧ UnaryHistory directed ∧
        UnaryHistory refinement ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
          Cont index baseElement directed ∧ Cont directed refinement replay ∧
            Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier
  obtain ⟨indexUnary, baseUnary, refinementUnary, transportUnary, _localNameUnary,
    indexBaseDirected, directedRefinementReplay, transportReplayProvenance,
    provenancePkg, localNamePkg⟩ := carrier
  have directedUnary : UnaryHistory directed :=
    unary_cont_closed indexUnary baseUnary indexBaseDirected
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed directedUnary refinementUnary directedRefinementReplay
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed transportUnary replayUnary transportReplayProvenance
  exact
    ⟨indexUnary, baseUnary, directedUnary, refinementUnary, replayUnary,
      provenanceUnary, indexBaseDirected, directedRefinementReplay,
      transportReplayProvenance, provenancePkg, localNamePkg⟩

theorem FilterBaseCarrier_cauchyfilter_completion_handoff [AskSetup] [PackageSetup]
    {index baseElement directed refinement transport replay provenance localName handoff
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FilterBaseCarrier index baseElement directed refinement transport replay provenance
        localName bundle pkg ->
      Cont replay provenance handoff ->
        Cont handoff localName completionRead ->
          PkgSig bundle completionRead pkg ->
            UnaryHistory index ∧ UnaryHistory baseElement ∧ UnaryHistory directed ∧
              UnaryHistory refinement ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
                UnaryHistory handoff ∧ UnaryHistory completionRead ∧
                  Cont index baseElement directed ∧ Cont directed refinement replay ∧
                    Cont transport replay provenance ∧ Cont replay provenance handoff ∧
                      Cont handoff localName completionRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle localName pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier replayProvenanceHandoff handoffLocalCompletion completionPkg
  obtain ⟨indexUnary, baseUnary, refinementUnary, transportUnary, localNameUnary,
    indexBaseDirected, directedRefinementReplay, transportReplayProvenance,
    provenancePkg, localNamePkg⟩ := carrier
  have directedUnary : UnaryHistory directed :=
    unary_cont_closed indexUnary baseUnary indexBaseDirected
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed directedUnary refinementUnary directedRefinementReplay
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed transportUnary replayUnary transportReplayProvenance
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed replayUnary provenanceUnary replayProvenanceHandoff
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed handoffUnary localNameUnary handoffLocalCompletion
  exact
    ⟨indexUnary, baseUnary, directedUnary, refinementUnary, replayUnary, provenanceUnary,
      handoffUnary, completionUnary, indexBaseDirected, directedRefinementReplay,
      transportReplayProvenance, replayProvenanceHandoff, handoffLocalCompletion,
      provenancePkg, localNamePkg, completionPkg⟩

theorem FilterBaseCarrier_directed_refinement_coverage [AskSetup] [PackageSetup]
    {index baseElement directed refinement transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FilterBaseCarrier index baseElement directed refinement transport replay provenance
        localName bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row index ∨ hsame row baseElement ∨ hsame row directed ∨
              hsame row refinement ∨ hsame row replay)
          (fun row : BHist =>
            hsame row index ∨ hsame row baseElement ∨ hsame row directed ∨
              hsame row refinement ∨ hsame row replay)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧
              (hsame row index ∨ hsame row baseElement ∨ hsame row directed ∨
                hsame row refinement ∨ hsame row replay))
          hsame ∧
        UnaryHistory directed ∧ UnaryHistory replay ∧ Cont index baseElement directed ∧
          Cont directed refinement replay ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert UnaryHistory Cont
  intro carrier
  obtain ⟨indexUnary, baseUnary, refinementUnary, _transportUnary, _localNameUnary,
    indexBaseDirected, directedRefinementReplay, _transportReplayProvenance,
    provenancePkg, _localNamePkg⟩ := carrier
  have directedUnary : UnaryHistory directed :=
    unary_cont_closed indexUnary baseUnary indexBaseDirected
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed directedUnary refinementUnary directedRefinementReplay
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row index ∨ hsame row baseElement ∨ hsame row directed ∨
              hsame row refinement ∨ hsame row replay)
          (fun row : BHist =>
            hsame row index ∨ hsame row baseElement ∨ hsame row directed ∨
              hsame row refinement ∨ hsame row replay)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧
              (hsame row index ∨ hsame row baseElement ∨ hsame row directed ∨
                hsame row refinement ∨ hsame row replay))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro index (Or.inl (hsame_refl index))
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
        intro row row' sameRows source
        cases source with
        | inl sameIndex =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameIndex)
        | inr rest =>
            cases rest with
            | inl sameBase =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameBase))
            | inr rest =>
                cases rest with
                | inl sameDirected =>
                    exact
                      Or.inr
                        (Or.inr
                          (Or.inl (hsame_trans (hsame_symm sameRows) sameDirected)))
                | inr rest =>
                    cases rest with
                    | inl sameRefinement =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl
                                  (hsame_trans (hsame_symm sameRows) sameRefinement))))
                    | inr sameReplay =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr (hsame_trans (hsame_symm sameRows) sameReplay))))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, source⟩
  }
  exact
    ⟨cert, directedUnary, replayUnary, indexBaseDirected, directedRefinementReplay,
      provenancePkg⟩

theorem FilterBaseCarrier_refinement_stability [AskSetup] [PackageSetup]
    {index baseElement directed refinement transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FilterBaseCarrier index baseElement directed refinement transport replay provenance
        localName bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row refinement ∨ hsame row replay ∨
            hsame row provenance)
          (fun row : BHist => hsame row refinement ∨ hsame row replay ∨
            hsame row provenance)
          (fun row : BHist =>
            PkgSig bundle localName pkg ∧
              (hsame row refinement ∨ hsame row replay ∨ hsame row provenance))
          hsame ∧
        UnaryHistory refinement ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
          Cont directed refinement replay ∧ Cont transport replay provenance ∧
            PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert UnaryHistory Cont
  intro carrier
  obtain ⟨indexUnary, baseUnary, refinementUnary, transportUnary, _localNameUnary,
    indexBaseDirected, directedRefinementReplay, transportReplayProvenance,
    _provenancePkg, localNamePkg⟩ := carrier
  have directedUnary : UnaryHistory directed :=
    unary_cont_closed indexUnary baseUnary indexBaseDirected
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed directedUnary refinementUnary directedRefinementReplay
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed transportUnary replayUnary transportReplayProvenance
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refinement ∨ hsame row replay ∨
            hsame row provenance)
          (fun row : BHist => hsame row refinement ∨ hsame row replay ∨
            hsame row provenance)
          (fun row : BHist =>
            PkgSig bundle localName pkg ∧
              (hsame row refinement ∨ hsame row replay ∨ hsame row provenance))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refinement (Or.inl (hsame_refl refinement))
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
        intro row row' sameRows source
        cases source with
        | inl sameRefinement =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameRefinement)
        | inr rest =>
            cases rest with
            | inl sameReplay =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameReplay))
            | inr sameProvenance =>
                exact
                  Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameProvenance))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact ⟨localNamePkg, source⟩
  }
  exact
    ⟨cert, refinementUnary, replayUnary, provenanceUnary, directedRefinementReplay,
      transportReplayProvenance, localNamePkg⟩

theorem FilterBaseCarrier_completion_branch_coverage [AskSetup] [PackageSetup]
    {index baseElement directed refinement transport replay provenance localName handoff
      completionRead branchRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FilterBaseCarrier index baseElement directed refinement transport replay provenance
        localName bundle pkg ->
      Cont replay provenance handoff ->
        Cont handoff localName completionRead ->
          Cont directed refinement branchRead ->
            PkgSig bundle completionRead pkg ->
              PkgSig bundle branchRead pkg ->
                UnaryHistory directed ∧ UnaryHistory refinement ∧ UnaryHistory replay ∧
                  UnaryHistory provenance ∧ UnaryHistory handoff ∧
                    UnaryHistory completionRead ∧ UnaryHistory branchRead ∧
                      Cont directed refinement replay ∧ Cont replay provenance handoff ∧
                        Cont handoff localName completionRead ∧
                          Cont directed refinement branchRead ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle completionRead pkg ∧
                                PkgSig bundle branchRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier replayProvenanceHandoff handoffLocalCompletion
    directedRefinementBranch completionPkg branchPkg
  obtain ⟨indexUnary, baseUnary, refinementUnary, transportUnary, localNameUnary,
    indexBaseDirected, directedRefinementReplay, transportReplayProvenance,
    provenancePkg, _localNamePkg⟩ := carrier
  have directedUnary : UnaryHistory directed :=
    unary_cont_closed indexUnary baseUnary indexBaseDirected
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed directedUnary refinementUnary directedRefinementReplay
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed transportUnary replayUnary transportReplayProvenance
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed replayUnary provenanceUnary replayProvenanceHandoff
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed handoffUnary localNameUnary handoffLocalCompletion
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed directedUnary refinementUnary directedRefinementBranch
  exact
    ⟨directedUnary, refinementUnary, replayUnary, provenanceUnary, handoffUnary,
      completionUnary, branchUnary, directedRefinementReplay, replayProvenanceHandoff,
      handoffLocalCompletion, directedRefinementBranch, provenancePkg, completionPkg,
      branchPkg⟩

theorem FilterBaseCarrier_classifier_stability [AskSetup] [PackageSetup]
    {index baseElement directed refinement transport replay provenance localName index'
      baseElement' directed' refinement' transport' replay' provenance' localName' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FilterBaseCarrier index baseElement directed refinement transport replay provenance
        localName bundle pkg ->
      hsame index index' ->
        hsame baseElement baseElement' ->
          hsame refinement refinement' ->
            hsame transport transport' ->
              hsame localName localName' ->
                Cont index' baseElement' directed' ->
                  Cont directed' refinement' replay' ->
                    Cont transport' replay' provenance' ->
                      PkgSig bundle provenance' pkg ->
                        PkgSig bundle localName' pkg ->
                          FilterBaseCarrier index' baseElement' directed' refinement'
                              transport' replay' provenance' localName' bundle pkg ∧
                            hsame directed directed' ∧ hsame replay replay' ∧
                              hsame provenance provenance' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame UnaryHistory Cont PkgSig
  intro carrier sameIndex sameBase sameRefinement sameTransport sameLocalName
    indexBaseDirected' directedRefinementReplay' transportReplayProvenance'
    provenancePkg' localNamePkg'
  obtain ⟨indexUnary, baseUnary, refinementUnary, transportUnary, localNameUnary,
    indexBaseDirected, directedRefinementReplay, transportReplayProvenance,
    _provenancePkg, _localNamePkg⟩ := carrier
  have indexUnary' : UnaryHistory index' :=
    unary_transport indexUnary sameIndex
  have baseUnary' : UnaryHistory baseElement' :=
    unary_transport baseUnary sameBase
  have refinementUnary' : UnaryHistory refinement' :=
    unary_transport refinementUnary sameRefinement
  have transportUnary' : UnaryHistory transport' :=
    unary_transport transportUnary sameTransport
  have localNameUnary' : UnaryHistory localName' :=
    unary_transport localNameUnary sameLocalName
  have sameDirected : hsame directed directed' :=
    cont_respects_hsame sameIndex sameBase indexBaseDirected indexBaseDirected'
  have sameReplay : hsame replay replay' :=
    cont_respects_hsame sameDirected sameRefinement directedRefinementReplay
      directedRefinementReplay'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameTransport sameReplay transportReplayProvenance
      transportReplayProvenance'
  have carrier' :
      FilterBaseCarrier index' baseElement' directed' refinement' transport' replay'
          provenance' localName' bundle pkg :=
    ⟨indexUnary', baseUnary', refinementUnary', transportUnary', localNameUnary',
      indexBaseDirected', directedRefinementReplay', transportReplayProvenance',
      provenancePkg', localNamePkg'⟩
  exact ⟨carrier', sameDirected, sameReplay, sameProvenance⟩

end BEDC.Derived.FilterBaseUp
