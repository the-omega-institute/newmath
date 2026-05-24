import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FilterBaseUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.FilterBaseUp
