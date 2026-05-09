import BEDC.GroundCompiler.EventFlow
import BEDC.GroundCompiler.SemanticMotif

namespace BEDC.GroundCompiler.CaseStudies

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.SemanticMotif

def PrefixSubflow (M S : EventFlow) : Prop :=
  exists tail : EventFlow, S = List.append M tail

def ZeroRunEvent : Nat -> RawEvent
  | 0 => [BMark.b0]
  | n + 1 => BMark.b0 :: ZeroRunEvent n

def FiniteRepetitionSkeleton : Nat -> EventFlow
  | 0 => []
  | n + 1 => List.append (FiniteRepetitionSkeleton n) [ZeroRunEvent n]

def NatLikeSkeleton (k : Nat) : EventFlow :=
  List.append (FiniteRepetitionSkeleton k) [[BMark.b0, BMark.b1]]

theorem nat_like_extends_repetition (k : Nat) :
    PrefixSubflow (FiniteRepetitionSkeleton k) (NatLikeSkeleton k) := by
  exact ⟨[[BMark.b0, BMark.b1]], rfl⟩

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
