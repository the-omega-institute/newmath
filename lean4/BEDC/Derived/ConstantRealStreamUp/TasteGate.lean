import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstantRealStreamUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstantRealStreamUp : Type where
  | mk (Q D S R E H C P N : BHist) : ConstantRealStreamUp
  deriving DecidableEq

def constantRealStreamEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constantRealStreamEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constantRealStreamEncodeBHist h

def constantRealStreamDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constantRealStreamDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constantRealStreamDecodeBHist tail)

theorem ConstantRealStreamTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, constantRealStreamDecodeBHist (constantRealStreamEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def constantRealStreamFields : ConstantRealStreamUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConstantRealStreamUp.mk Q D S R E H C P N => [Q, D, S, R, E, H, C, P, N]

def constantRealStreamToEventFlow : ConstantRealStreamUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (constantRealStreamFields x).map constantRealStreamEncodeBHist

def constantRealStreamEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => constantRealStreamEventAt index rest

def constantRealStreamFromEventFlow (ef : EventFlow) : Option ConstantRealStreamUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConstantRealStreamUp.mk
      (constantRealStreamDecodeBHist (constantRealStreamEventAt 0 ef))
      (constantRealStreamDecodeBHist (constantRealStreamEventAt 1 ef))
      (constantRealStreamDecodeBHist (constantRealStreamEventAt 2 ef))
      (constantRealStreamDecodeBHist (constantRealStreamEventAt 3 ef))
      (constantRealStreamDecodeBHist (constantRealStreamEventAt 4 ef))
      (constantRealStreamDecodeBHist (constantRealStreamEventAt 5 ef))
      (constantRealStreamDecodeBHist (constantRealStreamEventAt 6 ef))
      (constantRealStreamDecodeBHist (constantRealStreamEventAt 7 ef))
      (constantRealStreamDecodeBHist (constantRealStreamEventAt 8 ef)))

theorem ConstantRealStreamTasteGate_single_carrier_alignment_round_trip
    (x : ConstantRealStreamUp) :
    constantRealStreamFromEventFlow (constantRealStreamToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Q D S R E H C P N =>
      change
        some
          (ConstantRealStreamUp.mk
            (constantRealStreamDecodeBHist (constantRealStreamEncodeBHist Q))
            (constantRealStreamDecodeBHist (constantRealStreamEncodeBHist D))
            (constantRealStreamDecodeBHist (constantRealStreamEncodeBHist S))
            (constantRealStreamDecodeBHist (constantRealStreamEncodeBHist R))
            (constantRealStreamDecodeBHist (constantRealStreamEncodeBHist E))
            (constantRealStreamDecodeBHist (constantRealStreamEncodeBHist H))
            (constantRealStreamDecodeBHist (constantRealStreamEncodeBHist C))
            (constantRealStreamDecodeBHist (constantRealStreamEncodeBHist P))
            (constantRealStreamDecodeBHist (constantRealStreamEncodeBHist N))) =
          some (ConstantRealStreamUp.mk Q D S R E H C P N)
      rw [ConstantRealStreamTasteGate_single_carrier_alignment_decode_encode Q,
        ConstantRealStreamTasteGate_single_carrier_alignment_decode_encode D,
        ConstantRealStreamTasteGate_single_carrier_alignment_decode_encode S,
        ConstantRealStreamTasteGate_single_carrier_alignment_decode_encode R,
        ConstantRealStreamTasteGate_single_carrier_alignment_decode_encode E,
        ConstantRealStreamTasteGate_single_carrier_alignment_decode_encode H,
        ConstantRealStreamTasteGate_single_carrier_alignment_decode_encode C,
        ConstantRealStreamTasteGate_single_carrier_alignment_decode_encode P,
        ConstantRealStreamTasteGate_single_carrier_alignment_decode_encode N]

theorem ConstantRealStreamTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ConstantRealStreamUp} :
    constantRealStreamToEventFlow x = constantRealStreamToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      constantRealStreamFromEventFlow (constantRealStreamToEventFlow x) =
        constantRealStreamFromEventFlow (constantRealStreamToEventFlow y) :=
    congrArg constantRealStreamFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ConstantRealStreamTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ConstantRealStreamTasteGate_single_carrier_alignment_round_trip y)))

theorem ConstantRealStreamTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : ConstantRealStreamUp, constantRealStreamFields x = constantRealStreamFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Q₁ D₁ S₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk Q₂ D₂ S₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance constantRealStreamBHistCarrier : BHistCarrier ConstantRealStreamUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constantRealStreamToEventFlow
  fromEventFlow := constantRealStreamFromEventFlow

instance constantRealStreamChapterTasteGate : ChapterTasteGate ConstantRealStreamUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change constantRealStreamFromEventFlow (constantRealStreamToEventFlow x) = some x
    exact ConstantRealStreamTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ConstantRealStreamTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance constantRealStreamFieldFaithful : FieldFaithful ConstantRealStreamUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := constantRealStreamFields
  field_faithful := ConstantRealStreamTasteGate_single_carrier_alignment_field_faithful

instance constantRealStreamNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ConstantRealStreamUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ConstantRealStreamUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ConstantRealStreamUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ConstantRealStreamUp :=
  -- BEDC touchpoint anchor: BHist BMark
  constantRealStreamChapterTasteGate

theorem ConstantRealStreamTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ConstantRealStreamUp) ∧
      Nonempty (FieldFaithful ConstantRealStreamUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial ConstantRealStreamUp) ∧
          (∀ h : BHist, constantRealStreamDecodeBHist (constantRealStreamEncodeBHist h) = h) ∧
            constantRealStreamEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨constantRealStreamChapterTasteGate⟩, ⟨constantRealStreamFieldFaithful⟩,
      ⟨constantRealStreamNontrivial⟩,
      ConstantRealStreamTasteGate_single_carrier_alignment_decode_encode, rfl⟩

end BEDC.Derived.ConstantRealStreamUp
