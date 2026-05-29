import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopFixedPointIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopFixedPointIntervalUp : Type where
  | mk (I T M B R E H C P N : BHist) : BishopFixedPointIntervalUp
  deriving DecidableEq

def bishopFixedPointIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopFixedPointIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopFixedPointIntervalEncodeBHist h

def bishopFixedPointIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopFixedPointIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopFixedPointIntervalDecodeBHist tail)

private theorem bishopFixedPointInterval_decode_encode_bhist :
    ∀ h : BHist,
      bishopFixedPointIntervalDecodeBHist (bishopFixedPointIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopFixedPointIntervalFields : BishopFixedPointIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopFixedPointIntervalUp.mk I T M B R E H C P N => [I, T, M, B, R, E, H, C, P, N]

def bishopFixedPointIntervalToEventFlow : BishopFixedPointIntervalUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bishopFixedPointIntervalFields x).map bishopFixedPointIntervalEncodeBHist

private def bishopFixedPointIntervalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopFixedPointIntervalEventAtDefault index rest

def bishopFixedPointIntervalFromEventFlow
    (ef : EventFlow) : Option BishopFixedPointIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopFixedPointIntervalUp.mk
      (bishopFixedPointIntervalDecodeBHist (bishopFixedPointIntervalEventAtDefault 0 ef))
      (bishopFixedPointIntervalDecodeBHist (bishopFixedPointIntervalEventAtDefault 1 ef))
      (bishopFixedPointIntervalDecodeBHist (bishopFixedPointIntervalEventAtDefault 2 ef))
      (bishopFixedPointIntervalDecodeBHist (bishopFixedPointIntervalEventAtDefault 3 ef))
      (bishopFixedPointIntervalDecodeBHist (bishopFixedPointIntervalEventAtDefault 4 ef))
      (bishopFixedPointIntervalDecodeBHist (bishopFixedPointIntervalEventAtDefault 5 ef))
      (bishopFixedPointIntervalDecodeBHist (bishopFixedPointIntervalEventAtDefault 6 ef))
      (bishopFixedPointIntervalDecodeBHist (bishopFixedPointIntervalEventAtDefault 7 ef))
      (bishopFixedPointIntervalDecodeBHist (bishopFixedPointIntervalEventAtDefault 8 ef))
      (bishopFixedPointIntervalDecodeBHist (bishopFixedPointIntervalEventAtDefault 9 ef)))

private theorem bishopFixedPointInterval_round_trip :
    ∀ x : BishopFixedPointIntervalUp,
      bishopFixedPointIntervalFromEventFlow
        (bishopFixedPointIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I T M B R E H C P N =>
      change
        some
          (BishopFixedPointIntervalUp.mk
            (bishopFixedPointIntervalDecodeBHist (bishopFixedPointIntervalEncodeBHist I))
            (bishopFixedPointIntervalDecodeBHist (bishopFixedPointIntervalEncodeBHist T))
            (bishopFixedPointIntervalDecodeBHist (bishopFixedPointIntervalEncodeBHist M))
            (bishopFixedPointIntervalDecodeBHist (bishopFixedPointIntervalEncodeBHist B))
            (bishopFixedPointIntervalDecodeBHist (bishopFixedPointIntervalEncodeBHist R))
            (bishopFixedPointIntervalDecodeBHist (bishopFixedPointIntervalEncodeBHist E))
            (bishopFixedPointIntervalDecodeBHist (bishopFixedPointIntervalEncodeBHist H))
            (bishopFixedPointIntervalDecodeBHist (bishopFixedPointIntervalEncodeBHist C))
            (bishopFixedPointIntervalDecodeBHist (bishopFixedPointIntervalEncodeBHist P))
            (bishopFixedPointIntervalDecodeBHist (bishopFixedPointIntervalEncodeBHist N))) =
          some (BishopFixedPointIntervalUp.mk I T M B R E H C P N)
      rw [bishopFixedPointInterval_decode_encode_bhist I,
        bishopFixedPointInterval_decode_encode_bhist T,
        bishopFixedPointInterval_decode_encode_bhist M,
        bishopFixedPointInterval_decode_encode_bhist B,
        bishopFixedPointInterval_decode_encode_bhist R,
        bishopFixedPointInterval_decode_encode_bhist E,
        bishopFixedPointInterval_decode_encode_bhist H,
        bishopFixedPointInterval_decode_encode_bhist C,
        bishopFixedPointInterval_decode_encode_bhist P,
        bishopFixedPointInterval_decode_encode_bhist N]

private theorem bishopFixedPointIntervalToEventFlow_injective
    {x y : BishopFixedPointIntervalUp} :
    bishopFixedPointIntervalToEventFlow x =
      bishopFixedPointIntervalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopFixedPointIntervalFromEventFlow
          (bishopFixedPointIntervalToEventFlow x) =
        bishopFixedPointIntervalFromEventFlow
          (bishopFixedPointIntervalToEventFlow y) :=
    congrArg bishopFixedPointIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopFixedPointInterval_round_trip x).symm
      (Eq.trans hread (bishopFixedPointInterval_round_trip y)))

private theorem bishopFixedPointInterval_field_faithful :
    ∀ x y : BishopFixedPointIntervalUp,
      bishopFixedPointIntervalFields x = bishopFixedPointIntervalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I T M B R E H C P N =>
      cases y with
      | mk I' T' M' B' R' E' H' C' P' N' =>
          cases hfields
          rfl

instance bishopFixedPointIntervalBHistCarrier : BHistCarrier BishopFixedPointIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopFixedPointIntervalToEventFlow
  fromEventFlow := bishopFixedPointIntervalFromEventFlow

instance bishopFixedPointIntervalChapterTasteGate :
    ChapterTasteGate BishopFixedPointIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopFixedPointIntervalFromEventFlow (bishopFixedPointIntervalToEventFlow x) = some x
    exact bishopFixedPointInterval_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopFixedPointIntervalToEventFlow_injective heq)

instance bishopFixedPointIntervalFieldFaithful : FieldFaithful BishopFixedPointIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopFixedPointIntervalFields
  field_faithful := bishopFixedPointInterval_field_faithful

instance bishopFixedPointIntervalNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BishopFixedPointIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopFixedPointIntervalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopFixedPointIntervalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopFixedPointIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopFixedPointIntervalChapterTasteGate

theorem BishopFixedPointIntervalTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BishopFixedPointIntervalUp) ∧
      Nonempty (FieldFaithful BishopFixedPointIntervalUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial BishopFixedPointIntervalUp) ∧
      (∀ h : BHist,
        bishopFixedPointIntervalDecodeBHist
          (bishopFixedPointIntervalEncodeBHist h) = h) ∧
      (∀ x : BishopFixedPointIntervalUp,
        bishopFixedPointIntervalFromEventFlow
          (bishopFixedPointIntervalToEventFlow x) = some x) ∧
      (∀ x y : BishopFixedPointIntervalUp,
        bishopFixedPointIntervalToEventFlow x =
          bishopFixedPointIntervalToEventFlow y → x = y) ∧
      bishopFixedPointIntervalEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨bishopFixedPointIntervalChapterTasteGate⟩,
      ⟨bishopFixedPointIntervalFieldFaithful⟩,
      ⟨bishopFixedPointIntervalNontrivial⟩,
      bishopFixedPointInterval_decode_encode_bhist,
      bishopFixedPointInterval_round_trip,
      (fun _ _ heq => bishopFixedPointIntervalToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BishopFixedPointIntervalUp
