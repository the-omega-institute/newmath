import BEDC.GroundCompiler.EventFlow

namespace BEDC.GroundCompiler.SelfHostingCompilerFlow

open BEDC.GroundCompiler.EventFlow

def CompilerCandidateFlow : Type := EventFlow

def CompilerRecognitionRelation
    (R C : CompilerCandidateFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow R C)

def CompilerBehaviorRelation : Type :=
  CompilerCandidateFlow -> EventFlow -> EventFlow -> Prop

def CompilerCertificateCandidateFlow : Type := EventFlow

def CompilerCertificateRecognition
    (RK : EventFlow) (KC : CompilerCertificateCandidateFlow)
    (C : CompilerCandidateFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow RK KC) /\
    FormalCompilerInput (CompilerDatum.eventFlow C)

def CertifiedCompiler (C : CompilerCandidateFlow) : Prop :=
  exists KC : CompilerCertificateCandidateFlow,
    exists RK : EventFlow, CompilerCertificateRecognition RK KC C

def FormalCompilationJudgment
    (Compiles : CompilerBehaviorRelation)
    (C : CompilerCandidateFlow) (S T : EventFlow) : Prop :=
  CertifiedCompiler C /\ Compiles C S T

theorem uncertified_cannot_compile
    {Compiles : CompilerBehaviorRelation}
    {C : CompilerCandidateFlow} {S T : EventFlow} :
    Not (CertifiedCompiler C) ->
      Not (FormalCompilationJudgment Compiles C S T) := by
  intro hUncertified hJudgment
  exact hUncertified hJudgment.left

end BEDC.GroundCompiler.SelfHostingCompilerFlow
