import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyMajorantSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyMajorantSequenceCarrier [AskSetup] [PackageSetup]
    (source modulus window dyadic majorant handoff realSeal transport replay
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory source ∧ UnaryHistory modulus ∧ UnaryHistory window ∧
    UnaryHistory dyadic ∧ UnaryHistory majorant ∧ UnaryHistory handoff ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ Cont source modulus window ∧
        Cont window dyadic majorant ∧ Cont majorant handoff realSeal ∧
          Cont transport replay localName ∧ PkgSig bundle localName pkg

theorem CauchyMajorantSequenceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source modulus window dyadic majorant handoff realSeal transport replay
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyMajorantSequenceCarrier source modulus window dyadic majorant handoff realSeal
        transport replay localName bundle pkg ->
      UnaryHistory source ∧ UnaryHistory modulus ∧ UnaryHistory window ∧
        UnaryHistory dyadic ∧ UnaryHistory majorant ∧ UnaryHistory handoff ∧
          UnaryHistory realSeal ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
            UnaryHistory localName ∧ Cont source modulus window ∧
              Cont window dyadic majorant ∧ Cont majorant handoff realSeal ∧
                Cont transport replay localName ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier
  obtain ⟨sourceUnary, modulusUnary, windowUnary, dyadicUnary, majorantUnary,
    handoffUnary, transportUnary, replayUnary, sourceModulusWindow, windowDyadicMajorant,
    majorantHandoffRealSeal, transportReplayLocalName, localNamePkg⟩ := carrier
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed majorantUnary handoffUnary majorantHandoffRealSeal
  have localNameUnary : UnaryHistory localName :=
    unary_cont_closed transportUnary replayUnary transportReplayLocalName
  exact
    ⟨sourceUnary, modulusUnary, windowUnary, dyadicUnary, majorantUnary, handoffUnary,
      realSealUnary, transportUnary, replayUnary, localNameUnary, sourceModulusWindow,
      windowDyadicMajorant, majorantHandoffRealSeal, transportReplayLocalName, localNamePkg⟩

theorem CauchyMajorantSequenceCarrier_regseqrat_handoff [AskSetup] [PackageSetup]
    {source modulus window dyadic majorant handoff realSeal transport replay localName
      handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyMajorantSequenceCarrier source modulus window dyadic majorant handoff realSeal
        transport replay localName bundle pkg ->
      Cont handoff localName handoffRead ->
        PkgSig bundle handoffRead pkg ->
          UnaryHistory source ∧ UnaryHistory modulus ∧ UnaryHistory window ∧
            UnaryHistory dyadic ∧ UnaryHistory majorant ∧ UnaryHistory handoff ∧
              UnaryHistory handoffRead ∧ Cont source modulus window ∧
                Cont window dyadic majorant ∧ Cont majorant handoff realSeal ∧
                  Cont handoff localName handoffRead ∧ PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier handoffLocalNameRead handoffReadPkg
  have obligations :=
    CauchyMajorantSequenceCarrier_namecert_obligations
      (source := source) (modulus := modulus) (window := window) (dyadic := dyadic)
      (majorant := majorant) (handoff := handoff) (realSeal := realSeal)
      (transport := transport) (replay := replay) (localName := localName)
      (bundle := bundle) (pkg := pkg) carrier
  obtain ⟨sourceUnary, modulusUnary, windowUnary, dyadicUnary, majorantUnary,
    handoffUnary, _realSealUnary, _transportUnary, _replayUnary, localNameUnary,
    sourceModulusWindow, windowDyadicMajorant, majorantHandoffRealSeal,
    _transportReplayLocalName, _localNamePkg⟩ := obligations
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed handoffUnary localNameUnary handoffLocalNameRead
  exact
    ⟨sourceUnary, modulusUnary, windowUnary, dyadicUnary, majorantUnary, handoffUnary,
      handoffReadUnary, sourceModulusWindow, windowDyadicMajorant, majorantHandoffRealSeal,
      handoffLocalNameRead, handoffReadPkg⟩

end BEDC.Derived.CauchyMajorantSequenceUp
