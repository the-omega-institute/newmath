import BEDC.Derived.RealSequenceLimitUp

namespace BEDC.Derived.RealSequenceLimitUp.RegularCauchyTailFactorization

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealSequenceLimitRegularCauchyTailFactorization [AskSetup] [PackageSetup]
    {sequence limit window dyadic classifier transport replay provenance name criterionTail
      regularTail realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RealSequenceLimitUp sequence limit window dyadic classifier transport replay
        provenance name bundle pkg ->
      Cont classifier window criterionTail ->
        Cont criterionTail replay regularTail ->
          Cont regularTail transport realSeal ->
            PkgSig bundle realSeal pkg ->
              UnaryHistory window ∧ UnaryHistory dyadic ∧ UnaryHistory classifier ∧
                UnaryHistory criterionTail ∧ UnaryHistory regularTail ∧
                  UnaryHistory realSeal ∧ Cont classifier window criterionTail ∧
                    Cont criterionTail replay regularTail ∧
                      Cont regularTail transport realSeal ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier classifierWindowTail criterionTailReplayRegular regularTailTransportSeal
    realSealPkg
  rcases carrier with
    ⟨_sequenceUnary, _limitUnary, windowUnary, dyadicUnary, classifierUnary,
      transportUnary, replayUnary, _provenanceUnary, _nameUnary, _sequenceWindowReplay,
      _limitDyadicClassifier, _transportSame, _replaySame, _provenancePkg, namePkg⟩
  have criterionTailUnary : UnaryHistory criterionTail :=
    unary_cont_closed classifierUnary windowUnary classifierWindowTail
  have regularTailUnary : UnaryHistory regularTail :=
    unary_cont_closed criterionTailUnary replayUnary criterionTailReplayRegular
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regularTailUnary transportUnary regularTailTransportSeal
  exact
    ⟨windowUnary, dyadicUnary, classifierUnary, criterionTailUnary, regularTailUnary,
      realSealUnary, classifierWindowTail, criterionTailReplayRegular, regularTailTransportSeal,
      namePkg, realSealPkg⟩

end BEDC.Derived.RealSequenceLimitUp.RegularCauchyTailFactorization
