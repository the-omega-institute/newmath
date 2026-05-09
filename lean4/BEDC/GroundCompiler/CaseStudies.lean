import BEDC.GroundCompiler.EventFlow

namespace BEDC.GroundCompiler.CaseStudies

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow

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

end BEDC.GroundCompiler.CaseStudies
