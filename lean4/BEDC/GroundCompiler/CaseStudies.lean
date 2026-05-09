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
  | addLike
  | foldLike
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

theorem repetition_skeleton_not_repeat_rule :
    Not (RepeatRuleMotif (FiniteRepetitionSkeleton 3)) := by
  intro h
  cases h with
  | intro tail ht =>
      cases tail <;> cases ht

theorem prefix_subflow_subflow {M S : EventFlow} :
    PrefixSubflow M S -> Subflow M S := by
  intro h
  cases h with
  | intro tail ht =>
      exact Or.inl ⟨[], tail, by simpa using ht⟩

theorem prefix_subflow_self (S : EventFlow) :
    PrefixSubflow S S := by
  exact ⟨[], by simp⟩

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

theorem add_fold_not_license :
    exists A B : CaseStudyFlow,
      A.flow = AddSkeleton /\
        B.flow = FoldSkeleton /\
        PrefixSubflow A.flow B.flow /\
        Not (A.target = B.target) := by
  refine
    ⟨{ flow := AddSkeleton, target := CaseStudyTarget.addLike },
      { flow := FoldSkeleton, target := CaseStudyTarget.foldLike }, ?_⟩
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · exact fold_skeleton_extends_add
      · intro h
        cases h

def ListSpineSkeleton (a : RawEvent) (k : Nat) : EventFlow :=
  FiniteRepetitionPrefix a k

def ListConstructorLedgerMotif
    (R S spine ledger payloadSource payloadClassifier decomposition :
      EventFlow) :
    Prop :=
  RecognizesMotif R S spine ReuseRole /\
    Subflow ledger S /\
    Subflow payloadSource S /\
    Subflow payloadClassifier S /\
    Subflow decomposition S /\
    NonemptyEventFlow ledger

theorem list_finite_plus_ledger
    {R S spine ledger payloadSource payloadClassifier decomposition :
      EventFlow} :
    ListConstructorLedgerMotif R S spine ledger payloadSource
      payloadClassifier decomposition ->
      RecognizesMotif R S spine ReuseRole /\ NonemptyEventFlow ledger := by
  intro h
  exact ⟨h.left, h.right.right.right.right.right⟩

theorem zero_run_append (k : Nat) :
    List.append (ZeroRunEvent k) [BMark.b0] =
      BMark.b0 :: ZeroRunEvent k := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      change
        BMark.b0 :: List.append (ZeroRunEvent k) [BMark.b0] =
        BMark.b0 :: BMark.b0 :: ZeroRunEvent k
      exact congrArg (fun xs => BMark.b0 :: xs) ih

theorem zero_repeat_raw_event (k : Nat) :
    RepeatRawEvent [BMark.b0] k = ZeroRunEvent k := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      simp only [RepeatRawEvent]
      rw [ih, zero_run_append]
      rfl

theorem list_spine_shares_repetition_with_nat (k : Nat) :
    ListSpineSkeleton [BMark.b0] k = FiniteRepetitionSkeleton k := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      change
        List.append (FiniteRepetitionPrefix [BMark.b0] k)
          [RepeatRawEvent [BMark.b0] k] =
        List.append (FiniteRepetitionSkeleton k) [ZeroRunEvent k]
      rw [zero_repeat_raw_event k]
      change
        List.append (ListSpineSkeleton [BMark.b0] k) [ZeroRunEvent k] =
        List.append (FiniteRepetitionSkeleton k) [ZeroRunEvent k]
      rw [ih]

theorem same_finite_spine_not_same_object :
    exists A B : CaseStudyFlow,
      PrefixSubflow (FiniteRepetitionSkeleton 3) A.flow /\
        PrefixSubflow (FiniteRepetitionSkeleton 3) B.flow /\
        A.flow = B.flow /\
        Not (A.target = B.target) := by
  let spine := FiniteRepetitionSkeleton 3
  refine
    ⟨{ flow := spine, target := CaseStudyTarget.finiteRepetition },
      { flow := spine, target := CaseStudyTarget.listLike }, ?_⟩
  constructor
  · exact prefix_subflow_self spine
  · constructor
    · exact prefix_subflow_self spine
    · constructor
      · rfl
      · intro h
        cases h

def CompletionSkeleton : EventFlow :=
  List.append (FiniteRepetitionSkeleton 3)
    [[BMark.b0, BMark.b1],
      [BMark.b0, BMark.b1, BMark.b1],
      [BMark.b1, BMark.b0, BMark.b0]]

theorem completion_skeleton_contains_repetition :
    PrefixSubflow (FiniteRepetitionSkeleton 3) CompletionSkeleton := by
  exact
    ⟨[[BMark.b0, BMark.b1],
      [BMark.b0, BMark.b1, BMark.b1],
      [BMark.b1, BMark.b0, BMark.b0]], rfl⟩

theorem completion_skeleton_contains_carry :
    Subflow
      [[BMark.b0, BMark.b1, BMark.b1],
        [BMark.b1, BMark.b0, BMark.b0]]
      CompletionSkeleton := by
  exact
    Or.inl
      ⟨List.append (FiniteRepetitionSkeleton 3) [[BMark.b0, BMark.b1]], [],
        rfl⟩

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

def CompletionMotif (S : EventFlow) : Prop :=
  exists M : CompletionMotifRecord, RecognizedCompletionMotifRecord S M

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

def sameDisplayMark : DisplayAlphabet -> DisplayAlphabet -> Bool
  | BMark.b0, BMark.b0 => true
  | BMark.b1, BMark.b1 => true
  | _, _ => false

def sameRawEvent : RawEvent -> RawEvent -> Bool
  | [], [] => true
  | m :: ms, n :: ns =>
      match sameDisplayMark m n with
      | true => sameRawEvent ms ns
      | false => false
  | _, _ => false

def PrefixLen : EventFlow -> EventFlow -> Nat
  | [], _ => 0
  | _, [] => 0
  | w :: ws, v :: vs =>
      match sameRawEvent w v with
      | true => Nat.succ (PrefixLen ws vs)
      | false => 0

def RecognizedMotifOverlap
    (S T : EventFlow) (R : GeneratedMotifRecognizer) (M : EventFlow)
    (mu : MotifRole) : Prop :=
  RecognizesMotif R S M mu /\ RecognizesMotif R T M mu

structure SkeletonOverlap (S T : EventFlow) where
  rawPrefixOverlap : Nat
  rawPrefixOverlap_eq : rawPrefixOverlap = PrefixLen S T
  motifOverlap : GeneratedMotifRecognizer -> EventFlow -> MotifRole -> Prop
  motifOverlap_iff :
    forall R M mu, motifOverlap R M mu <-> RecognizedMotifOverlap S T R M mu

def skeletonOverlap (S T : EventFlow) : SkeletonOverlap S T where
  rawPrefixOverlap := PrefixLen S T
  rawPrefixOverlap_eq := rfl
  motifOverlap := RecognizedMotifOverlap S T
  motifOverlap_iff := by
    intro R M mu
    rfl

theorem fold_completion_prefix :
    PrefixLen FoldSkeleton CompletionSkeleton = 2 := by
  rfl

theorem fold_completion_share_starting_prefix :
    PrefixSubflow (FiniteRepetitionSkeleton 2) FoldSkeleton /\
      PrefixSubflow (FiniteRepetitionSkeleton 2) CompletionSkeleton := by
  constructor
  · exact
      ⟨[[BMark.b0, BMark.b0, BMark.b1],
        [BMark.b0, BMark.b0, BMark.b1, BMark.b1],
        [BMark.b0, BMark.b1, BMark.b0, BMark.b0]], rfl⟩
  · exact
      ⟨[[BMark.b0, BMark.b0, BMark.b0],
        [BMark.b0, BMark.b1],
        [BMark.b0, BMark.b1, BMark.b1],
        [BMark.b1, BMark.b0, BMark.b0]], rfl⟩

theorem fold_completion_split :
    PrefixLen FoldSkeleton CompletionSkeleton = 2 /\
      Not (PrefixSubflow FoldSkeleton CompletionSkeleton) /\
      Not (PrefixSubflow CompletionSkeleton FoldSkeleton) := by
  constructor
  · exact fold_completion_prefix
  · constructor
    · intro h
      cases h with
      | intro tail ht =>
          cases tail <;> cases ht
    · intro h
      cases h with
      | intro tail ht =>
          cases tail <;> cases ht

theorem nat_prefix_completion :
    PrefixSubflow (NatLikeSkeleton 3) CompletionSkeleton := by
  exact
    ⟨[[BMark.b0, BMark.b1, BMark.b1],
      [BMark.b1, BMark.b0, BMark.b0]], rfl⟩

theorem completion_extends_nat_like :
    PrefixSubflow (NatLikeSkeleton 3) CompletionSkeleton /\
      Subflow
        [[BMark.b0, BMark.b1, BMark.b1],
          [BMark.b1, BMark.b0, BMark.b0]]
        CompletionSkeleton := by
  exact ⟨nat_prefix_completion, completion_skeleton_contains_carry⟩

theorem skeleton_extension_not_object_extension :
    exists A B : CaseStudyFlow,
      PrefixSubflow A.flow B.flow /\ Not (A.target = B.target) := by
  refine
    ⟨{ flow := NatLikeSkeleton 3, target := CaseStudyTarget.finiteRepetition },
      { flow := CompletionSkeleton, target := CaseStudyTarget.completion }, ?_⟩
  constructor
  · exact nat_prefix_completion
  · intro h
    cases h

structure SkeletonMotifReport where
  sourceFlow : EventFlow
  profileFlow : EventFlow
  supportFlow : EventFlow
  ledgerFlow : EventFlow
  metricFlow : EventFlow

theorem skeleton_reports_not_certificates :
    exists report : SkeletonMotifReport,
      FormalCompilerInput (CompilerDatum.eventFlow report.sourceFlow) /\
        Not (AcceptedObjectFlow report.sourceFlow) := by
  exact
    ⟨{ sourceFlow := [],
        profileFlow := [],
        supportFlow := [],
        ledgerFlow := [],
        metricFlow := [] },
      FormalCompilerInput.eventFlow [],
      empty_not_accepted_object_flow⟩

def CaseStudyFlowUsesOnlyDisplayAlphabet (S : EventFlow) : Prop :=
  forall w : RawEvent, List.Mem w S ->
    forall m : DisplayAlphabet, List.Mem m w -> m = BMark.b0 \/ m = BMark.b1

theorem comparison_not_proof :
    exists S T : EventFlow,
      PrefixLen S T = 2 /\ Not (S = T) := by
  refine ⟨FoldSkeleton, CompletionSkeleton, fold_completion_prefix, ?_⟩
  intro h
  have hPrefix : PrefixSubflow FoldSkeleton CompletionSkeleton :=
    ⟨[], by simp [h]⟩
  exact fold_completion_split.right.left hPrefix

theorem case_studies_conservativity :
    CaseStudyFlowUsesOnlyDisplayAlphabet AddSkeleton /\
      CaseStudyFlowUsesOnlyDisplayAlphabet FoldSkeleton /\
      CaseStudyFlowUsesOnlyDisplayAlphabet CompletionSkeleton := by
  constructor
  · intro _ _ m _
    cases m with
    | b0 => exact Or.inl rfl
    | b1 => exact Or.inr rfl
  · constructor
    · intro _ _ m _
      cases m with
      | b0 => exact Or.inl rfl
      | b1 => exact Or.inr rfl
    · intro _ _ m _
      cases m with
      | b0 => exact Or.inl rfl
      | b1 => exact Or.inr rfl

end BEDC.GroundCompiler.CaseStudies
