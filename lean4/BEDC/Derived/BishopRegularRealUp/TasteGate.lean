import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopRegularRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopRegularRealUp : Type where
  | mk (S M L Q R H C P N : BHist) : BishopRegularRealUp
  deriving DecidableEq

def bishopRegularRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopRegularRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopRegularRealEncodeBHist h

def bishopRegularRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopRegularRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopRegularRealDecodeBHist tail)

private theorem BishopRegularRealTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, bishopRegularRealDecodeBHist (bishopRegularRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopRegularRealFields : BishopRegularRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRegularRealUp.mk S M L Q R H C P N => [S, M, L, Q, R, H, C, P, N]

def bishopRegularRealToEventFlow : BishopRegularRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopRegularRealFields x).map bishopRegularRealEncodeBHist

private def bishopRegularRealEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopRegularRealEventAtDefault index rest

def bishopRegularRealFromEventFlow (ef : EventFlow) : Option BishopRegularRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopRegularRealUp.mk
      (bishopRegularRealDecodeBHist (bishopRegularRealEventAtDefault 0 ef))
      (bishopRegularRealDecodeBHist (bishopRegularRealEventAtDefault 1 ef))
      (bishopRegularRealDecodeBHist (bishopRegularRealEventAtDefault 2 ef))
      (bishopRegularRealDecodeBHist (bishopRegularRealEventAtDefault 3 ef))
      (bishopRegularRealDecodeBHist (bishopRegularRealEventAtDefault 4 ef))
      (bishopRegularRealDecodeBHist (bishopRegularRealEventAtDefault 5 ef))
      (bishopRegularRealDecodeBHist (bishopRegularRealEventAtDefault 6 ef))
      (bishopRegularRealDecodeBHist (bishopRegularRealEventAtDefault 7 ef))
      (bishopRegularRealDecodeBHist (bishopRegularRealEventAtDefault 8 ef)))

private theorem BishopRegularRealTasteGate_single_carrier_alignment_round_trip
    (x : BishopRegularRealUp) :
    bishopRegularRealFromEventFlow (bishopRegularRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S M L Q R H C P N =>
      change
        some
          (BishopRegularRealUp.mk
            (bishopRegularRealDecodeBHist (bishopRegularRealEncodeBHist S))
            (bishopRegularRealDecodeBHist (bishopRegularRealEncodeBHist M))
            (bishopRegularRealDecodeBHist (bishopRegularRealEncodeBHist L))
            (bishopRegularRealDecodeBHist (bishopRegularRealEncodeBHist Q))
            (bishopRegularRealDecodeBHist (bishopRegularRealEncodeBHist R))
            (bishopRegularRealDecodeBHist (bishopRegularRealEncodeBHist H))
            (bishopRegularRealDecodeBHist (bishopRegularRealEncodeBHist C))
            (bishopRegularRealDecodeBHist (bishopRegularRealEncodeBHist P))
            (bishopRegularRealDecodeBHist (bishopRegularRealEncodeBHist N))) =
          some (BishopRegularRealUp.mk S M L Q R H C P N)
      rw [BishopRegularRealTasteGate_single_carrier_alignment_decode_encode S,
        BishopRegularRealTasteGate_single_carrier_alignment_decode_encode M,
        BishopRegularRealTasteGate_single_carrier_alignment_decode_encode L,
        BishopRegularRealTasteGate_single_carrier_alignment_decode_encode Q,
        BishopRegularRealTasteGate_single_carrier_alignment_decode_encode R,
        BishopRegularRealTasteGate_single_carrier_alignment_decode_encode H,
        BishopRegularRealTasteGate_single_carrier_alignment_decode_encode C,
        BishopRegularRealTasteGate_single_carrier_alignment_decode_encode P,
        BishopRegularRealTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopRegularRealTasteGate_single_carrier_alignment_injective
    {x y : BishopRegularRealUp} :
    bishopRegularRealToEventFlow x = bishopRegularRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopRegularRealFromEventFlow (bishopRegularRealToEventFlow x) =
        bishopRegularRealFromEventFlow (bishopRegularRealToEventFlow y) :=
    congrArg bishopRegularRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopRegularRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopRegularRealTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopRegularRealTasteGate_single_carrier_alignment_fields :
    ∀ x y : BishopRegularRealUp, bishopRegularRealFields x = bishopRegularRealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ M₁ L₁ Q₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ M₂ L₂ Q₂ R₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance bishopRegularRealBHistCarrier : BHistCarrier BishopRegularRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopRegularRealToEventFlow
  fromEventFlow := bishopRegularRealFromEventFlow

instance bishopRegularRealChapterTasteGate : ChapterTasteGate BishopRegularRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopRegularRealFromEventFlow (bishopRegularRealToEventFlow x) = some x
    exact BishopRegularRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopRegularRealTasteGate_single_carrier_alignment_injective heq)

instance bishopRegularRealFieldFaithful : FieldFaithful BishopRegularRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopRegularRealFields
  field_faithful := BishopRegularRealTasteGate_single_carrier_alignment_fields

instance bishopRegularRealNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BishopRegularRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopRegularRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopRegularRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BishopRegularRealTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BishopRegularRealUp) ∧
      Nonempty (FieldFaithful BishopRegularRealUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial BishopRegularRealUp) ∧
          (∀ h : BHist, bishopRegularRealDecodeBHist (bishopRegularRealEncodeBHist h) = h) ∧
            (∀ x : BishopRegularRealUp,
              bishopRegularRealFromEventFlow (bishopRegularRealToEventFlow x) = some x) ∧
              bishopRegularRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨bishopRegularRealChapterTasteGate⟩,
      ⟨⟨bishopRegularRealFieldFaithful⟩,
        ⟨⟨bishopRegularRealNontrivial⟩,
          ⟨BishopRegularRealTasteGate_single_carrier_alignment_decode_encode,
            ⟨BishopRegularRealTasteGate_single_carrier_alignment_round_trip, rfl⟩⟩⟩⟩⟩

end BEDC.Derived.BishopRegularRealUp
