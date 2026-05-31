import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealSequenceLimitUp [AskSetup] [PackageSetup]
    (sequence limit window dyadic classifier transport replay provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sequence ∧ UnaryHistory limit ∧ UnaryHistory window ∧
    UnaryHistory dyadic ∧ UnaryHistory classifier ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont sequence window replay ∧ Cont limit dyadic classifier ∧
          hsame transport BHist.Empty ∧ hsame replay classifier ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

end BEDC.Derived

namespace BEDC.Derived.RealSequenceLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealSequenceLimitCauchyCriterionFactorization [AskSetup] [PackageSetup]
    {sequence limit window dyadic classifier transport replay provenance name criterionTail
      realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RealSequenceLimitUp sequence limit window dyadic classifier transport replay
        provenance name bundle pkg ->
      Cont classifier window criterionTail ->
        Cont criterionTail replay realSeal ->
          PkgSig bundle realSeal pkg ->
            UnaryHistory window ∧ UnaryHistory dyadic ∧ UnaryHistory classifier ∧
              UnaryHistory criterionTail ∧ UnaryHistory realSeal ∧
                Cont classifier window criterionTail ∧ Cont criterionTail replay realSeal ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier classifierWindowTail criterionTailReplaySeal realSealPkg
  rcases carrier with
    ⟨_sequenceUnary, _limitUnary, windowUnary, dyadicUnary, classifierUnary,
      _transportUnary, replayUnary, _provenanceUnary, nameUnary, _sequenceWindowReplay,
      _limitDyadicClassifier, _transportSame, _replaySame, _provenancePkg, namePkg⟩
  have criterionTailUnary : UnaryHistory criterionTail :=
    unary_cont_closed classifierUnary windowUnary classifierWindowTail
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed criterionTailUnary replayUnary criterionTailReplaySeal
  exact
    ⟨windowUnary, dyadicUnary, classifierUnary, criterionTailUnary, realSealUnary,
      classifierWindowTail, criterionTailReplaySeal, namePkg, realSealPkg⟩

end BEDC.Derived.RealSequenceLimitUp
