import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LebesgueStieltjesMeasureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LebesgueStieltjesMeasureUp : Type where
  | mk (B S I A K R E H C P N : BHist) : LebesgueStieltjesMeasureUp
  deriving DecidableEq

def lebesgueStieltjesMeasureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lebesgueStieltjesMeasureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lebesgueStieltjesMeasureEncodeBHist h

def lebesgueStieltjesMeasureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lebesgueStieltjesMeasureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lebesgueStieltjesMeasureDecodeBHist tail)

private theorem LebesgueStieltjesMeasureTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      lebesgueStieltjesMeasureDecodeBHist (lebesgueStieltjesMeasureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lebesgueStieltjesMeasureFields : LebesgueStieltjesMeasureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LebesgueStieltjesMeasureUp.mk B S I A K R E H C P N => [B, S, I, A, K, R, E, H, C, P, N]

def lebesgueStieltjesMeasureToEventFlow : LebesgueStieltjesMeasureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (lebesgueStieltjesMeasureFields x).map lebesgueStieltjesMeasureEncodeBHist

private def lebesgueStieltjesMeasureEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lebesgueStieltjesMeasureEventAt index rest

def lebesgueStieltjesMeasureFromEventFlow
    (ef : EventFlow) : Option LebesgueStieltjesMeasureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LebesgueStieltjesMeasureUp.mk
      (lebesgueStieltjesMeasureDecodeBHist (lebesgueStieltjesMeasureEventAt 0 ef))
      (lebesgueStieltjesMeasureDecodeBHist (lebesgueStieltjesMeasureEventAt 1 ef))
      (lebesgueStieltjesMeasureDecodeBHist (lebesgueStieltjesMeasureEventAt 2 ef))
      (lebesgueStieltjesMeasureDecodeBHist (lebesgueStieltjesMeasureEventAt 3 ef))
      (lebesgueStieltjesMeasureDecodeBHist (lebesgueStieltjesMeasureEventAt 4 ef))
      (lebesgueStieltjesMeasureDecodeBHist (lebesgueStieltjesMeasureEventAt 5 ef))
      (lebesgueStieltjesMeasureDecodeBHist (lebesgueStieltjesMeasureEventAt 6 ef))
      (lebesgueStieltjesMeasureDecodeBHist (lebesgueStieltjesMeasureEventAt 7 ef))
      (lebesgueStieltjesMeasureDecodeBHist (lebesgueStieltjesMeasureEventAt 8 ef))
      (lebesgueStieltjesMeasureDecodeBHist (lebesgueStieltjesMeasureEventAt 9 ef))
      (lebesgueStieltjesMeasureDecodeBHist (lebesgueStieltjesMeasureEventAt 10 ef)))

private theorem LebesgueStieltjesMeasureTasteGate_single_carrier_alignment_round_trip
    (x : LebesgueStieltjesMeasureUp) :
    lebesgueStieltjesMeasureFromEventFlow (lebesgueStieltjesMeasureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B S I A K R E H C P N =>
      change
        some
          (LebesgueStieltjesMeasureUp.mk
            (lebesgueStieltjesMeasureDecodeBHist (lebesgueStieltjesMeasureEncodeBHist B))
            (lebesgueStieltjesMeasureDecodeBHist (lebesgueStieltjesMeasureEncodeBHist S))
            (lebesgueStieltjesMeasureDecodeBHist (lebesgueStieltjesMeasureEncodeBHist I))
            (lebesgueStieltjesMeasureDecodeBHist (lebesgueStieltjesMeasureEncodeBHist A))
            (lebesgueStieltjesMeasureDecodeBHist (lebesgueStieltjesMeasureEncodeBHist K))
            (lebesgueStieltjesMeasureDecodeBHist (lebesgueStieltjesMeasureEncodeBHist R))
            (lebesgueStieltjesMeasureDecodeBHist (lebesgueStieltjesMeasureEncodeBHist E))
            (lebesgueStieltjesMeasureDecodeBHist (lebesgueStieltjesMeasureEncodeBHist H))
            (lebesgueStieltjesMeasureDecodeBHist (lebesgueStieltjesMeasureEncodeBHist C))
            (lebesgueStieltjesMeasureDecodeBHist (lebesgueStieltjesMeasureEncodeBHist P))
            (lebesgueStieltjesMeasureDecodeBHist (lebesgueStieltjesMeasureEncodeBHist N))) =
          some (LebesgueStieltjesMeasureUp.mk B S I A K R E H C P N)
      rw [LebesgueStieltjesMeasureTasteGate_single_carrier_alignment_decode_encode B,
        LebesgueStieltjesMeasureTasteGate_single_carrier_alignment_decode_encode S,
        LebesgueStieltjesMeasureTasteGate_single_carrier_alignment_decode_encode I,
        LebesgueStieltjesMeasureTasteGate_single_carrier_alignment_decode_encode A,
        LebesgueStieltjesMeasureTasteGate_single_carrier_alignment_decode_encode K,
        LebesgueStieltjesMeasureTasteGate_single_carrier_alignment_decode_encode R,
        LebesgueStieltjesMeasureTasteGate_single_carrier_alignment_decode_encode E,
        LebesgueStieltjesMeasureTasteGate_single_carrier_alignment_decode_encode H,
        LebesgueStieltjesMeasureTasteGate_single_carrier_alignment_decode_encode C,
        LebesgueStieltjesMeasureTasteGate_single_carrier_alignment_decode_encode P,
        LebesgueStieltjesMeasureTasteGate_single_carrier_alignment_decode_encode N]

private theorem lebesgueStieltjesMeasureToEventFlow_injective
    {x y : LebesgueStieltjesMeasureUp} :
    lebesgueStieltjesMeasureToEventFlow x = lebesgueStieltjesMeasureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lebesgueStieltjesMeasureFromEventFlow (lebesgueStieltjesMeasureToEventFlow x) =
        lebesgueStieltjesMeasureFromEventFlow (lebesgueStieltjesMeasureToEventFlow y) :=
    congrArg lebesgueStieltjesMeasureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LebesgueStieltjesMeasureTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LebesgueStieltjesMeasureTasteGate_single_carrier_alignment_round_trip y)))

private theorem LebesgueStieltjesMeasureTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : LebesgueStieltjesMeasureUp,
      lebesgueStieltjesMeasureFields x = lebesgueStieltjesMeasureFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B₁ S₁ I₁ A₁ K₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ S₂ I₂ A₂ K₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance lebesgueStieltjesMeasureBHistCarrier : BHistCarrier LebesgueStieltjesMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lebesgueStieltjesMeasureToEventFlow
  fromEventFlow := lebesgueStieltjesMeasureFromEventFlow

instance lebesgueStieltjesMeasureChapterTasteGate :
    ChapterTasteGate LebesgueStieltjesMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lebesgueStieltjesMeasureFromEventFlow (lebesgueStieltjesMeasureToEventFlow x) = some x
    exact LebesgueStieltjesMeasureTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (lebesgueStieltjesMeasureToEventFlow_injective heq)

instance lebesgueStieltjesMeasureFieldFaithful :
    FieldFaithful LebesgueStieltjesMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := lebesgueStieltjesMeasureFields
  field_faithful := LebesgueStieltjesMeasureTasteGate_single_carrier_alignment_fields_faithful

instance lebesgueStieltjesMeasureNontrivial : Nontrivial LebesgueStieltjesMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LebesgueStieltjesMeasureUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      LebesgueStieltjesMeasureUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def LebesgueStieltjesMeasureTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate LebesgueStieltjesMeasureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  lebesgueStieltjesMeasureChapterTasteGate

theorem LebesgueStieltjesMeasureTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      lebesgueStieltjesMeasureDecodeBHist (lebesgueStieltjesMeasureEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LebesgueStieltjesMeasureUp) ∧
        Nonempty (ChapterTasteGate LebesgueStieltjesMeasureUp) ∧
          lebesgueStieltjesMeasureEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨LebesgueStieltjesMeasureTasteGate_single_carrier_alignment_decode_encode,
      ⟨lebesgueStieltjesMeasureBHistCarrier⟩,
      ⟨lebesgueStieltjesMeasureChapterTasteGate⟩, rfl⟩

end BEDC.Derived.LebesgueStieltjesMeasureUp
