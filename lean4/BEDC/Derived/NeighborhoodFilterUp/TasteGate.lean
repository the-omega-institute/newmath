import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NeighborhoodFilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NeighborhoodFilterUp : Type where
  | mk (X x O B D C M T H K P N : BHist) : NeighborhoodFilterUp
  deriving DecidableEq

def neighborhoodFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: neighborhoodFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: neighborhoodFilterEncodeBHist h

def neighborhoodFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (neighborhoodFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (neighborhoodFilterDecodeBHist tail)

private theorem NeighborhoodFilterTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, neighborhoodFilterDecodeBHist (neighborhoodFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def neighborhoodFilterToEventFlow : NeighborhoodFilterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NeighborhoodFilterUp.mk X x O B D C M T H K P N =>
      [[BMark.b1, BMark.b0, BMark.b1],
        neighborhoodFilterEncodeBHist X,
        neighborhoodFilterEncodeBHist x,
        neighborhoodFilterEncodeBHist O,
        neighborhoodFilterEncodeBHist B,
        neighborhoodFilterEncodeBHist D,
        neighborhoodFilterEncodeBHist C,
        neighborhoodFilterEncodeBHist M,
        neighborhoodFilterEncodeBHist T,
        neighborhoodFilterEncodeBHist H,
        neighborhoodFilterEncodeBHist K,
        neighborhoodFilterEncodeBHist P,
        neighborhoodFilterEncodeBHist N]

private def neighborhoodFilterEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => neighborhoodFilterEventAtDefault index rest

def neighborhoodFilterFromEventFlow (ef : EventFlow) : Option NeighborhoodFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NeighborhoodFilterUp.mk
      (neighborhoodFilterDecodeBHist (neighborhoodFilterEventAtDefault 1 ef))
      (neighborhoodFilterDecodeBHist (neighborhoodFilterEventAtDefault 2 ef))
      (neighborhoodFilterDecodeBHist (neighborhoodFilterEventAtDefault 3 ef))
      (neighborhoodFilterDecodeBHist (neighborhoodFilterEventAtDefault 4 ef))
      (neighborhoodFilterDecodeBHist (neighborhoodFilterEventAtDefault 5 ef))
      (neighborhoodFilterDecodeBHist (neighborhoodFilterEventAtDefault 6 ef))
      (neighborhoodFilterDecodeBHist (neighborhoodFilterEventAtDefault 7 ef))
      (neighborhoodFilterDecodeBHist (neighborhoodFilterEventAtDefault 8 ef))
      (neighborhoodFilterDecodeBHist (neighborhoodFilterEventAtDefault 9 ef))
      (neighborhoodFilterDecodeBHist (neighborhoodFilterEventAtDefault 10 ef))
      (neighborhoodFilterDecodeBHist (neighborhoodFilterEventAtDefault 11 ef))
      (neighborhoodFilterDecodeBHist (neighborhoodFilterEventAtDefault 12 ef)))

private theorem NeighborhoodFilterTasteGate_single_carrier_alignment_round_trip :
    ∀ x : NeighborhoodFilterUp,
      neighborhoodFilterFromEventFlow (neighborhoodFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro z
  cases z with
  | mk X x O B D C M T H K P N =>
      change
        some
          (NeighborhoodFilterUp.mk
            (neighborhoodFilterDecodeBHist (neighborhoodFilterEncodeBHist X))
            (neighborhoodFilterDecodeBHist (neighborhoodFilterEncodeBHist x))
            (neighborhoodFilterDecodeBHist (neighborhoodFilterEncodeBHist O))
            (neighborhoodFilterDecodeBHist (neighborhoodFilterEncodeBHist B))
            (neighborhoodFilterDecodeBHist (neighborhoodFilterEncodeBHist D))
            (neighborhoodFilterDecodeBHist (neighborhoodFilterEncodeBHist C))
            (neighborhoodFilterDecodeBHist (neighborhoodFilterEncodeBHist M))
            (neighborhoodFilterDecodeBHist (neighborhoodFilterEncodeBHist T))
            (neighborhoodFilterDecodeBHist (neighborhoodFilterEncodeBHist H))
            (neighborhoodFilterDecodeBHist (neighborhoodFilterEncodeBHist K))
            (neighborhoodFilterDecodeBHist (neighborhoodFilterEncodeBHist P))
            (neighborhoodFilterDecodeBHist (neighborhoodFilterEncodeBHist N))) =
          some (NeighborhoodFilterUp.mk X x O B D C M T H K P N)
      rw [NeighborhoodFilterTasteGate_single_carrier_alignment_decode X,
        NeighborhoodFilterTasteGate_single_carrier_alignment_decode x,
        NeighborhoodFilterTasteGate_single_carrier_alignment_decode O,
        NeighborhoodFilterTasteGate_single_carrier_alignment_decode B,
        NeighborhoodFilterTasteGate_single_carrier_alignment_decode D,
        NeighborhoodFilterTasteGate_single_carrier_alignment_decode C,
        NeighborhoodFilterTasteGate_single_carrier_alignment_decode M,
        NeighborhoodFilterTasteGate_single_carrier_alignment_decode T,
        NeighborhoodFilterTasteGate_single_carrier_alignment_decode H,
        NeighborhoodFilterTasteGate_single_carrier_alignment_decode K,
        NeighborhoodFilterTasteGate_single_carrier_alignment_decode P,
        NeighborhoodFilterTasteGate_single_carrier_alignment_decode N]

private theorem NeighborhoodFilterTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : NeighborhoodFilterUp} :
    neighborhoodFilterToEventFlow x = neighborhoodFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      neighborhoodFilterFromEventFlow (neighborhoodFilterToEventFlow x) =
        neighborhoodFilterFromEventFlow (neighborhoodFilterToEventFlow y) :=
    congrArg neighborhoodFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (NeighborhoodFilterTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (NeighborhoodFilterTasteGate_single_carrier_alignment_round_trip y)))

private def neighborhoodFilterFields : NeighborhoodFilterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NeighborhoodFilterUp.mk X x O B D C M T H K P N => [X, x, O, B, D, C, M, T, H, K, P, N]

private theorem NeighborhoodFilterTasteGate_single_carrier_alignment_fields :
    ∀ x y : NeighborhoodFilterUp, neighborhoodFilterFields x = neighborhoodFilterFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro u v hfields
  cases u with
  | mk X1 x1 O1 B1 D1 C1 M1 T1 H1 K1 P1 N1 =>
      cases v with
      | mk X2 x2 O2 B2 D2 C2 M2 T2 H2 K2 P2 N2 =>
          cases hfields
          rfl

instance neighborhoodFilterBHistCarrier : BHistCarrier NeighborhoodFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := neighborhoodFilterToEventFlow
  fromEventFlow := neighborhoodFilterFromEventFlow

instance neighborhoodFilterChapterTasteGate : ChapterTasteGate NeighborhoodFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change neighborhoodFilterFromEventFlow (neighborhoodFilterToEventFlow x) = some x
    exact NeighborhoodFilterTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (NeighborhoodFilterTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance neighborhoodFilterFieldFaithful : FieldFaithful NeighborhoodFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := neighborhoodFilterFields
  field_faithful := NeighborhoodFilterTasteGate_single_carrier_alignment_fields

instance neighborhoodFilterNontrivial : Nontrivial NeighborhoodFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NeighborhoodFilterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      NeighborhoodFilterUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate NeighborhoodFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  neighborhoodFilterChapterTasteGate

theorem NeighborhoodFilterTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate NeighborhoodFilterUp) ∧
      Nonempty (FieldFaithful NeighborhoodFilterUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial NeighborhoodFilterUp) ∧
          (∀ h : BHist, neighborhoodFilterDecodeBHist (neighborhoodFilterEncodeBHist h) = h) ∧
            (∀ x : NeighborhoodFilterUp,
              neighborhoodFilterFromEventFlow (neighborhoodFilterToEventFlow x) =
                some x) ∧
              (∀ x y : NeighborhoodFilterUp,
                neighborhoodFilterToEventFlow x = neighborhoodFilterToEventFlow y → x = y) ∧
                neighborhoodFilterEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨neighborhoodFilterChapterTasteGate⟩,
      ⟨neighborhoodFilterFieldFaithful⟩,
      ⟨neighborhoodFilterNontrivial⟩,
      NeighborhoodFilterTasteGate_single_carrier_alignment_decode,
      NeighborhoodFilterTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => NeighborhoodFilterTasteGate_single_carrier_alignment_toEventFlow_injective
        heq),
      rfl⟩

end BEDC.Derived.NeighborhoodFilterUp
