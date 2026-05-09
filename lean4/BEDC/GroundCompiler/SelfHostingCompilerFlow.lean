import BEDC.GroundCompiler.EventFlow

namespace BEDC.GroundCompiler.SelfHostingCompilerFlow

open BEDC.GroundCompiler.EventFlow

def CompilerCandidateFlow : Type := EventFlow

def CompilerRecognitionRelation
    (R C : CompilerCandidateFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow R C)

def CompilerBehaviorRelation : Type :=
  CompilerCandidateFlow -> EventFlow -> EventFlow -> Prop

def CompilerTaskDomain (C D : CompilerCandidateFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow C D)

def CompilerTargetDomain (C T : CompilerCandidateFlow) : Prop :=
  FormalCompilerInput (CompilerDatum.recognizedFlow C T)

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

theorem formal_compilation_requires_certificate
    {Compiles : CompilerBehaviorRelation}
    {C : CompilerCandidateFlow} {S T : EventFlow} :
    FormalCompilationJudgment Compiles C S T -> CertifiedCompiler C := by
  intro hJudgment
  exact hJudgment.left

theorem uncertified_cannot_compile
    {Compiles : CompilerBehaviorRelation}
    {C : CompilerCandidateFlow} {S T : EventFlow} :
    Not (CertifiedCompiler C) ->
      Not (FormalCompilationJudgment Compiles C S T) := by
  intro hUncertified hJudgment
  exact hUncertified hJudgment.left

def P9Subflow (S C : EventFlow) : Prop :=
  exists pre : EventFlow, exists post : EventFlow,
    S = List.append (List.append pre C) post

def P9CompilerCandidate (S C : EventFlow) : Prop :=
  P9Subflow S C

def P9RecognizesCompiler (RC S C : EventFlow) : Prop :=
  P9CompilerCandidate S C /\
    FormalCompilerInput (CompilerDatum.recognizedFlow RC C)

def P9RecognizedCompilerFlow (S C : EventFlow) : Prop :=
  exists RC : EventFlow, P9RecognizesCompiler RC S C

def P9CompilerCertificateCandidate (S KC C : EventFlow) : Prop :=
  P9Subflow S KC /\ P9CompilerCandidate S C

def P9RecognizesCompilerCert (RK S KC C : EventFlow) : Prop :=
  P9CompilerCertificateCandidate S KC C /\
    FormalCompilerInput (CompilerDatum.recognizedFlow RK KC) /\
    P9RecognizedCompilerFlow S C

def P9CertifiedCompiler (C : EventFlow) : Prop :=
  exists S : EventFlow, exists KC : EventFlow, exists RK : EventFlow,
    P9RecognizesCompilerCert RK S KC C

def P9FormalCompilationJudgment
    (Compiles : CompilerBehaviorRelation)
    (C S T : EventFlow) : Prop :=
  P9CertifiedCompiler C /\ Compiles C S T

theorem p9_uncertified_cannot_compile
    {Compiles : CompilerBehaviorRelation}
    {C S T : EventFlow} :
    Not (P9CertifiedCompiler C) ->
      Not (P9FormalCompilationJudgment Compiles C S T) := by
  intro hUncertified hJudgment
  exact hUncertified hJudgment.left

end BEDC.GroundCompiler.SelfHostingCompilerFlow
