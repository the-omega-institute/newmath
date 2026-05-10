import BEDC.GroundCompiler.SelfHostingCompilerFlow

namespace BEDC.GroundCompiler.SelfHostingCompilerFlow

theorem remaining_obligations_block_full_discharge
    {behavior : CompilerBehaviorRelation} {C : CompilerCandidateFlow} :
    SelfHostingCompilerFlow behavior C ->
      BootstrapRecorded C ->
        SelfHostingCompilerFlow behavior C /\
          Not (FullyDischargedCompiler behavior C) := by
  intro hSelf hBootstrap
  exact ⟨hSelf, fun hFull => hFull.right.right hBootstrap⟩

inductive PrototypeLevel : Type where
  | p0
  | p1
  | p2
  | p3
  | p4
  | p5
  | p6
  | p7
  | p8
  | p9

inductive PrototypeStep : PrototypeLevel -> PrototypeLevel -> Prop where
  | p0_p1 : PrototypeStep PrototypeLevel.p0 PrototypeLevel.p1
  | p1_p2 : PrototypeStep PrototypeLevel.p1 PrototypeLevel.p2
  | p2_p3 : PrototypeStep PrototypeLevel.p2 PrototypeLevel.p3
  | p3_p4 : PrototypeStep PrototypeLevel.p3 PrototypeLevel.p4
  | p4_p5 : PrototypeStep PrototypeLevel.p4 PrototypeLevel.p5
  | p5_p6 : PrototypeStep PrototypeLevel.p5 PrototypeLevel.p6
  | p6_p7 : PrototypeStep PrototypeLevel.p6 PrototypeLevel.p7
  | p7_p8 : PrototypeStep PrototypeLevel.p7 PrototypeLevel.p8
  | p8_p9 : PrototypeStep PrototypeLevel.p8 PrototypeLevel.p9

def PrototypeLadder : Prop :=
  PrototypeStep PrototypeLevel.p0 PrototypeLevel.p1 /\
    PrototypeStep PrototypeLevel.p1 PrototypeLevel.p2 /\
    PrototypeStep PrototypeLevel.p2 PrototypeLevel.p3 /\
    PrototypeStep PrototypeLevel.p3 PrototypeLevel.p4 /\
    PrototypeStep PrototypeLevel.p4 PrototypeLevel.p5 /\
    PrototypeStep PrototypeLevel.p5 PrototypeLevel.p6 /\
    PrototypeStep PrototypeLevel.p6 PrototypeLevel.p7 /\
    PrototypeStep PrototypeLevel.p7 PrototypeLevel.p8 /\
    PrototypeStep PrototypeLevel.p8 PrototypeLevel.p9

theorem prototype_ladder : PrototypeLadder := by
  exact
    ⟨PrototypeStep.p0_p1, PrototypeStep.p1_p2, PrototypeStep.p2_p3,
      PrototypeStep.p3_p4, PrototypeStep.p4_p5, PrototypeStep.p5_p6,
      PrototypeStep.p6_p7, PrototypeStep.p7_p8, PrototypeStep.p8_p9⟩

inductive BelowP9 : PrototypeLevel -> Prop where
  | p0 : BelowP9 PrototypeLevel.p0
  | p1 : BelowP9 PrototypeLevel.p1
  | p2 : BelowP9 PrototypeLevel.p2
  | p3 : BelowP9 PrototypeLevel.p3
  | p4 : BelowP9 PrototypeLevel.p4
  | p5 : BelowP9 PrototypeLevel.p5
  | p6 : BelowP9 PrototypeLevel.p6
  | p7 : BelowP9 PrototypeLevel.p7
  | p8 : BelowP9 PrototypeLevel.p8

def FullNoHiddenCompilerClaimLevel (level : PrototypeLevel) : Prop :=
  level = PrototypeLevel.p9

theorem full_claim_p9_level {level : PrototypeLevel} :
    BelowP9 level -> Not (FullNoHiddenCompilerClaimLevel level) := by
  intro hBelow hFull
  cases hBelow <;> cases hFull

end BEDC.GroundCompiler.SelfHostingCompilerFlow
