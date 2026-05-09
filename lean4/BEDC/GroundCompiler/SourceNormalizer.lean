import BEDC.GroundCompiler.EventFlow

namespace BEDC.GroundCompiler.SourceNormalizer

open BEDC.GroundCompiler.EventFlow

inductive AdjPair : EventFlow -> Nat -> RawEvent -> RawEvent -> Prop where
  | here (w v : RawEvent) (rest : EventFlow) :
      AdjPair (w :: v :: rest) 0 w v
  | there (x : RawEvent) {S : EventFlow} {i : Nat} {w v : RawEvent} :
      AdjPair S i w v -> AdjPair (x :: S) (i + 1) w v

def NormCand
    (candidate : RawEvent -> RawEvent -> Prop)
    (S : EventFlow) (i : Nat) (w v : RawEvent) : Prop :=
  AdjPair S i w v /\ candidate w v

theorem adj_pair_events_mem {S : EventFlow} {i : Nat} {w v : RawEvent} :
    AdjPair S i w v -> List.Mem w S /\ List.Mem v S := by
  intro h
  induction h with
  | here w v rest =>
      constructor
      · exact List.Mem.head (v :: rest)
      · exact List.Mem.tail w (List.Mem.head rest)
  | there x h ih =>
      constructor
      · exact List.Mem.tail x ih.left
      · exact List.Mem.tail x ih.right

theorem candidate_preserves_raw
    {candidate : RawEvent -> RawEvent -> Prop}
    {S : EventFlow} {i : Nat} {w v : RawEvent} :
    NormCand candidate S i w v -> List.Mem w S /\ List.Mem v S := by
  intro h
  exact adj_pair_events_mem h.left

end BEDC.GroundCompiler.SourceNormalizer
