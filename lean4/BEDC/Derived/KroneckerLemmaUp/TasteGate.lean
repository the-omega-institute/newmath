import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KroneckerLemmaUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KroneckerLemmaUp : Type where
  | mk (T C A S W R B E H N : BHist) : KroneckerLemmaUp
  deriving DecidableEq

def kroneckerLemmaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kroneckerLemmaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kroneckerLemmaEncodeBHist h

def kroneckerLemmaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kroneckerLemmaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kroneckerLemmaDecodeBHist tail)

private theorem KroneckerLemmaTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, kroneckerLemmaDecodeBHist (kroneckerLemmaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kroneckerLemmaFields : KroneckerLemmaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KroneckerLemmaUp.mk T C A S W R B E H N => [T, C, A, S, W, R, B, E, H, N]

def kroneckerLemmaToEventFlow : KroneckerLemmaUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (kroneckerLemmaFields x).map kroneckerLemmaEncodeBHist

private def KroneckerLemmaTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      KroneckerLemmaTasteGate_single_carrier_alignment_eventAt index rest

def kroneckerLemmaFromEventFlow (ef : EventFlow) : Option KroneckerLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (KroneckerLemmaUp.mk
      (kroneckerLemmaDecodeBHist
        (KroneckerLemmaTasteGate_single_carrier_alignment_eventAt 0 ef))
      (kroneckerLemmaDecodeBHist
        (KroneckerLemmaTasteGate_single_carrier_alignment_eventAt 1 ef))
      (kroneckerLemmaDecodeBHist
        (KroneckerLemmaTasteGate_single_carrier_alignment_eventAt 2 ef))
      (kroneckerLemmaDecodeBHist
        (KroneckerLemmaTasteGate_single_carrier_alignment_eventAt 3 ef))
      (kroneckerLemmaDecodeBHist
        (KroneckerLemmaTasteGate_single_carrier_alignment_eventAt 4 ef))
      (kroneckerLemmaDecodeBHist
        (KroneckerLemmaTasteGate_single_carrier_alignment_eventAt 5 ef))
      (kroneckerLemmaDecodeBHist
        (KroneckerLemmaTasteGate_single_carrier_alignment_eventAt 6 ef))
      (kroneckerLemmaDecodeBHist
        (KroneckerLemmaTasteGate_single_carrier_alignment_eventAt 7 ef))
      (kroneckerLemmaDecodeBHist
        (KroneckerLemmaTasteGate_single_carrier_alignment_eventAt 8 ef))
      (kroneckerLemmaDecodeBHist
        (KroneckerLemmaTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem KroneckerLemmaTasteGate_single_carrier_alignment_round_trip
    (x : KroneckerLemmaUp) :
    kroneckerLemmaFromEventFlow (kroneckerLemmaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T C A S W R B E H N =>
      change
        some
          (KroneckerLemmaUp.mk
            (kroneckerLemmaDecodeBHist (kroneckerLemmaEncodeBHist T))
            (kroneckerLemmaDecodeBHist (kroneckerLemmaEncodeBHist C))
            (kroneckerLemmaDecodeBHist (kroneckerLemmaEncodeBHist A))
            (kroneckerLemmaDecodeBHist (kroneckerLemmaEncodeBHist S))
            (kroneckerLemmaDecodeBHist (kroneckerLemmaEncodeBHist W))
            (kroneckerLemmaDecodeBHist (kroneckerLemmaEncodeBHist R))
            (kroneckerLemmaDecodeBHist (kroneckerLemmaEncodeBHist B))
            (kroneckerLemmaDecodeBHist (kroneckerLemmaEncodeBHist E))
            (kroneckerLemmaDecodeBHist (kroneckerLemmaEncodeBHist H))
            (kroneckerLemmaDecodeBHist (kroneckerLemmaEncodeBHist N))) =
          some (KroneckerLemmaUp.mk T C A S W R B E H N)
      rw [KroneckerLemmaTasteGate_single_carrier_alignment_decode_encode T,
        KroneckerLemmaTasteGate_single_carrier_alignment_decode_encode C,
        KroneckerLemmaTasteGate_single_carrier_alignment_decode_encode A,
        KroneckerLemmaTasteGate_single_carrier_alignment_decode_encode S,
        KroneckerLemmaTasteGate_single_carrier_alignment_decode_encode W,
        KroneckerLemmaTasteGate_single_carrier_alignment_decode_encode R,
        KroneckerLemmaTasteGate_single_carrier_alignment_decode_encode B,
        KroneckerLemmaTasteGate_single_carrier_alignment_decode_encode E,
        KroneckerLemmaTasteGate_single_carrier_alignment_decode_encode H,
        KroneckerLemmaTasteGate_single_carrier_alignment_decode_encode N]

private theorem KroneckerLemmaTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : KroneckerLemmaUp} :
    kroneckerLemmaToEventFlow x = kroneckerLemmaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kroneckerLemmaFromEventFlow (kroneckerLemmaToEventFlow x) =
        kroneckerLemmaFromEventFlow (kroneckerLemmaToEventFlow y) :=
    congrArg kroneckerLemmaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (KroneckerLemmaTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (KroneckerLemmaTasteGate_single_carrier_alignment_round_trip y)))

private theorem KroneckerLemmaTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : KroneckerLemmaUp, kroneckerLemmaFields x = kroneckerLemmaFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T₁ C₁ A₁ S₁ W₁ R₁ B₁ E₁ H₁ N₁ =>
      cases y with
      | mk T₂ C₂ A₂ S₂ W₂ R₂ B₂ E₂ H₂ N₂ =>
          cases hfields
          rfl

instance kroneckerLemmaBHistCarrier : BHistCarrier KroneckerLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kroneckerLemmaToEventFlow
  fromEventFlow := kroneckerLemmaFromEventFlow

instance kroneckerLemmaChapterTasteGate : ChapterTasteGate KroneckerLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kroneckerLemmaFromEventFlow (kroneckerLemmaToEventFlow x) = some x
    exact KroneckerLemmaTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (KroneckerLemmaTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance kroneckerLemmaFieldFaithful : FieldFaithful KroneckerLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := kroneckerLemmaFields
  field_faithful := KroneckerLemmaTasteGate_single_carrier_alignment_fields_faithful

instance kroneckerLemmaNontrivial :
    BEDC.Meta.TasteGate.Nontrivial KroneckerLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨KroneckerLemmaUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      KroneckerLemmaUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def kroneckerLemmaTasteGate : ChapterTasteGate KroneckerLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kroneckerLemmaChapterTasteGate

theorem KroneckerLemmaTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate KroneckerLemmaUp) ∧
      Nonempty (FieldFaithful KroneckerLemmaUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial KroneckerLemmaUp) ∧
          (∀ h : BHist, kroneckerLemmaDecodeBHist (kroneckerLemmaEncodeBHist h) = h) ∧
            (∀ x : KroneckerLemmaUp,
              kroneckerLemmaFromEventFlow (kroneckerLemmaToEventFlow x) = some x) ∧
              (∀ x y : KroneckerLemmaUp,
                kroneckerLemmaToEventFlow x = kroneckerLemmaToEventFlow y → x = y) ∧
                kroneckerLemmaEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨kroneckerLemmaChapterTasteGate⟩,
      ⟨kroneckerLemmaFieldFaithful⟩,
      ⟨kroneckerLemmaNontrivial⟩,
      KroneckerLemmaTasteGate_single_carrier_alignment_decode_encode,
      KroneckerLemmaTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => KroneckerLemmaTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.KroneckerLemmaUp.TasteGate
