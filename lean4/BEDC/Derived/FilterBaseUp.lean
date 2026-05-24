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

end BEDC.Derived.FilterBaseUp
