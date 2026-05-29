import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PointwiseLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PointwiseLimitUp : Type where
  | mk (X Y F I S Q R E H C K N : BHist) : PointwiseLimitUp
  deriving DecidableEq

def pointwiseLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: pointwiseLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: pointwiseLimitEncodeBHist h

def pointwiseLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (pointwiseLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (pointwiseLimitDecodeBHist tail)

private theorem PointwiseLimitTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def pointwiseLimitFields : PointwiseLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PointwiseLimitUp.mk X Y F I S Q R E H C K N => [X, Y, F, I, S, Q, R, E, H, C, K, N]

def pointwiseLimitToEventFlow : PointwiseLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (pointwiseLimitFields x).map pointwiseLimitEncodeBHist

private def pointwiseLimitEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => pointwiseLimitEventAt index rest

def pointwiseLimitFromEventFlow (ef : EventFlow) : Option PointwiseLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PointwiseLimitUp.mk
      (pointwiseLimitDecodeBHist (pointwiseLimitEventAt 0 ef))
      (pointwiseLimitDecodeBHist (pointwiseLimitEventAt 1 ef))
      (pointwiseLimitDecodeBHist (pointwiseLimitEventAt 2 ef))
      (pointwiseLimitDecodeBHist (pointwiseLimitEventAt 3 ef))
      (pointwiseLimitDecodeBHist (pointwiseLimitEventAt 4 ef))
      (pointwiseLimitDecodeBHist (pointwiseLimitEventAt 5 ef))
      (pointwiseLimitDecodeBHist (pointwiseLimitEventAt 6 ef))
      (pointwiseLimitDecodeBHist (pointwiseLimitEventAt 7 ef))
      (pointwiseLimitDecodeBHist (pointwiseLimitEventAt 8 ef))
      (pointwiseLimitDecodeBHist (pointwiseLimitEventAt 9 ef))
      (pointwiseLimitDecodeBHist (pointwiseLimitEventAt 10 ef))
      (pointwiseLimitDecodeBHist (pointwiseLimitEventAt 11 ef)))

private theorem PointwiseLimitTasteGate_single_carrier_alignment_round_trip
    (x : PointwiseLimitUp) :
    pointwiseLimitFromEventFlow (pointwiseLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X Y F I S Q R E H C K N =>
      change
        some
          (PointwiseLimitUp.mk
            (pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist X))
            (pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist Y))
            (pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist F))
            (pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist I))
            (pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist S))
            (pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist Q))
            (pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist R))
            (pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist E))
            (pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist H))
            (pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist C))
            (pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist K))
            (pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist N))) =
          some (PointwiseLimitUp.mk X Y F I S Q R E H C K N)
      rw [PointwiseLimitTasteGate_single_carrier_alignment_decode_encode X,
        PointwiseLimitTasteGate_single_carrier_alignment_decode_encode Y,
        PointwiseLimitTasteGate_single_carrier_alignment_decode_encode F,
        PointwiseLimitTasteGate_single_carrier_alignment_decode_encode I,
        PointwiseLimitTasteGate_single_carrier_alignment_decode_encode S,
        PointwiseLimitTasteGate_single_carrier_alignment_decode_encode Q,
        PointwiseLimitTasteGate_single_carrier_alignment_decode_encode R,
        PointwiseLimitTasteGate_single_carrier_alignment_decode_encode E,
        PointwiseLimitTasteGate_single_carrier_alignment_decode_encode H,
        PointwiseLimitTasteGate_single_carrier_alignment_decode_encode C,
        PointwiseLimitTasteGate_single_carrier_alignment_decode_encode K,
        PointwiseLimitTasteGate_single_carrier_alignment_decode_encode N]

private theorem PointwiseLimitTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PointwiseLimitUp} :
    pointwiseLimitToEventFlow x = pointwiseLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      pointwiseLimitFromEventFlow (pointwiseLimitToEventFlow x) =
        pointwiseLimitFromEventFlow (pointwiseLimitToEventFlow y) :=
    congrArg pointwiseLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PointwiseLimitTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PointwiseLimitTasteGate_single_carrier_alignment_round_trip y)))

private theorem PointwiseLimitTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : PointwiseLimitUp, pointwiseLimitFields x = pointwiseLimitFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ Y₁ F₁ I₁ S₁ Q₁ R₁ E₁ H₁ C₁ K₁ N₁ =>
      cases y with
      | mk X₂ Y₂ F₂ I₂ S₂ Q₂ R₂ E₂ H₂ C₂ K₂ N₂ =>
          cases hfields
          rfl

instance pointwiseLimitBHistCarrier : BHistCarrier PointwiseLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := pointwiseLimitToEventFlow
  fromEventFlow := pointwiseLimitFromEventFlow

instance pointwiseLimitChapterTasteGate : ChapterTasteGate PointwiseLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change pointwiseLimitFromEventFlow (pointwiseLimitToEventFlow x) = some x
    exact PointwiseLimitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PointwiseLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance pointwiseLimitFieldFaithful : FieldFaithful PointwiseLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := pointwiseLimitFields
  field_faithful := PointwiseLimitTasteGate_single_carrier_alignment_fields_faithful

instance pointwiseLimitNontrivial :
    BEDC.Meta.TasteGate.Nontrivial PointwiseLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PointwiseLimitUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      PointwiseLimitUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def PointwiseLimitTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate PointwiseLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  pointwiseLimitChapterTasteGate

theorem PointwiseLimitTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate PointwiseLimitUp) ∧
      Nonempty (FieldFaithful PointwiseLimitUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial PointwiseLimitUp) ∧
          (∀ h : BHist, pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist h) = h) ∧
            (∀ x : PointwiseLimitUp,
              pointwiseLimitFromEventFlow (pointwiseLimitToEventFlow x) = some x) ∧
              pointwiseLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨pointwiseLimitChapterTasteGate⟩, ⟨pointwiseLimitFieldFaithful⟩,
      ⟨pointwiseLimitNontrivial⟩,
      PointwiseLimitTasteGate_single_carrier_alignment_decode_encode,
      PointwiseLimitTasteGate_single_carrier_alignment_round_trip, rfl⟩

end BEDC.Derived.PointwiseLimitUp
