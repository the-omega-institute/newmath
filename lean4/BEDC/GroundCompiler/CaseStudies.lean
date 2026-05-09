import BEDC.GroundCompiler.EventFlow
import BEDC.GroundCompiler.SemanticMotif

namespace BEDC.GroundCompiler.CaseStudies

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.SemanticMotif

def PrefixSubflow (M S : EventFlow) : Prop :=
  exists tail : EventFlow, S = List.append M tail

inductive CaseStudyTarget : Type where
  | finiteRepetition
  | addFold
  | completion
  | listLike

structure CaseStudyFlow where
  flow : EventFlow
  target : CaseStudyTarget

def SkeletonCode (S : EventFlow) : List DisplayAlphabet :=
  FlowEncoding S

def ZeroRunEvent : Nat -> RawEvent
  | 0 => [BMark.b0]
  | n + 1 => BMark.b0 :: ZeroRunEvent n

def FiniteRepetitionSkeleton : Nat -> EventFlow
  | 0 => []
  | n + 1 => List.append (FiniteRepetitionSkeleton n) [ZeroRunEvent n]

def CertifiedFiniteRepetitionRecognizer (R : GeneratedMotifRecognizer) : Prop :=
  FormalCompilerInput (CompilerDatum.eventFlow R)

def FiniteRepetitionMotifRecognition
    (R : GeneratedMotifRecognizer) (S M : EventFlow) : Prop :=
  CertifiedFiniteRepetitionRecognizer R /\
    RecognizesMotif R S M FiniteRepetitionRole

theorem subflow_self (S : EventFlow) : Subflow S S := by
  exact Or.inl ⟨[], [], by simp⟩

theorem repetition_skeleton_has_motif
    {R : GeneratedMotifRecognizer} (hR : CertifiedFiniteRepetitionRecognizer R)
    (k : Nat) :
    FiniteRepetitionMotifRecognition R
      (FiniteRepetitionSkeleton (k + 1)) (FiniteRepetitionSkeleton (k + 1)) := by
  constructor
  · exact hR
  · constructor
    · exact hR
    · constructor
      · constructor
        · exact FormalCompilerInput.eventFlow (FiniteRepetitionSkeleton (k + 1))
        · constructor
          · exact FormalCompilerInput.eventFlow (FiniteRepetitionSkeleton (k + 1))
          · exact FormalCompilerInput.eventFlow FiniteRepetitionRole
      · exact subflow_self (FiniteRepetitionSkeleton (k + 1))

def NatLikeSkeleton (k : Nat) : EventFlow :=
  List.append (FiniteRepetitionSkeleton k) [[BMark.b0, BMark.b1]]

def RepeatRuleMotif (S : EventFlow) : Prop :=
  PrefixSubflow (NatLikeSkeleton 3) S

theorem nat_like_extends_repetition (k : Nat) :
    PrefixSubflow (FiniteRepetitionSkeleton k) (NatLikeSkeleton k) := by
  exact ⟨[[BMark.b0, BMark.b1]], rfl⟩

theorem prefix_subflow_subflow {M S : EventFlow} :
    PrefixSubflow M S -> Subflow M S := by
  intro h
  cases h with
  | intro tail ht =>
      exact Or.inl ⟨[], tail, by simpa using ht⟩

theorem nat_repetition_share_prefix
    {R : GeneratedMotifRecognizer} (hR : CertifiedFiniteRepetitionRecognizer R)
    (k : Nat) :
    FiniteRepetitionMotifRecognition R (NatLikeSkeleton (k + 1))
      (FiniteRepetitionSkeleton (k + 1)) /\
    FiniteRepetitionMotifRecognition R
      (FiniteRepetitionSkeleton (k + 1)) (FiniteRepetitionSkeleton (k + 1)) := by
  constructor
  · constructor
    · exact hR
    · constructor
      · exact hR
      · constructor
        · constructor
          · exact FormalCompilerInput.eventFlow (NatLikeSkeleton (k + 1))
          · constructor
            · exact FormalCompilerInput.eventFlow (FiniteRepetitionSkeleton (k + 1))
            · exact FormalCompilerInput.eventFlow FiniteRepetitionRole
        · exact prefix_subflow_subflow (nat_like_extends_repetition (k + 1))
  · exact repetition_skeleton_has_motif hR k

def AddSkeleton : EventFlow :=
  [[BMark.b0], [BMark.b0, BMark.b0], [BMark.b0, BMark.b0, BMark.b1]]

def AdditiveRecursionMotif (S : EventFlow) : Prop :=
  PrefixSubflow AddSkeleton S

def FoldSkeleton : EventFlow :=
  List.append AddSkeleton
    [[BMark.b0, BMark.b0, BMark.b1, BMark.b1],
      [BMark.b0, BMark.b1, BMark.b0, BMark.b0]]

def FoldCompletionSegment : EventFlow :=
  [[BMark.b0, BMark.b0, BMark.b1],
    [BMark.b0, BMark.b0, BMark.b1, BMark.b1],
    [BMark.b0, BMark.b1, BMark.b0, BMark.b0]]

def FoldCompletionMotif (S : EventFlow) : Prop :=
  Subflow FoldCompletionSegment S

theorem fold_skeleton_extends_add :
    PrefixSubflow AddSkeleton FoldSkeleton := by
  exact
    ⟨[[BMark.b0, BMark.b0, BMark.b1, BMark.b1],
      [BMark.b0, BMark.b1, BMark.b0, BMark.b0]], rfl⟩

theorem fold_reuses_add :
    AdditiveRecursionMotif FoldSkeleton /\
      FoldCompletionMotif FoldSkeleton := by
  constructor
  · exact fold_skeleton_extends_add
  · exact Or.inl ⟨[[BMark.b0], [BMark.b0, BMark.b0]], [], rfl⟩

structure CompletionMotifRecord where
  stage : EventFlow
  threadFlow : EventFlow
  classifier : EventFlow
  sealFlow : EventFlow
  ledgerFlow : EventFlow

def RecognizedCompletionMotifRecord
    (S : EventFlow) (M : CompletionMotifRecord) : Prop :=
  Subflow M.stage S /\
    Subflow M.threadFlow S /\
    Subflow M.classifier S /\
    Subflow M.sealFlow S /\
    Subflow M.ledgerFlow S /\
    NonemptyEventFlow M.sealFlow /\
    NonemptyEventFlow M.ledgerFlow

def SealDepthAtLeastOne (S : EventFlow) : Prop :=
  exists sigma : EventFlow, Subflow sigma S /\ NonemptyEventFlow sigma

theorem completion_skeleton_seal_heavy
    {S : EventFlow} {M : CompletionMotifRecord} :
    RecognizedCompletionMotifRecord S M -> SealDepthAtLeastOne S := by
  intro h
  exact ⟨M.sealFlow, h.right.right.right.left, h.right.right.right.right.right.left⟩

theorem completion_skeleton_ledger_dependent
    {S : EventFlow} {M : CompletionMotifRecord} :
    Not (NonemptyEventFlow M.ledgerFlow) ->
      Not (RecognizedCompletionMotifRecord S M) := by
  intro hNoLedger hRecognized
  exact hNoLedger hRecognized.right.right.right.right.right.right

end BEDC.GroundCompiler.CaseStudies
