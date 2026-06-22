import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RieszInterpolationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RieszInterpolationUp : Type where
  | mk (G L P A B W H C S N : BHist) : RieszInterpolationUp
  deriving DecidableEq

def rieszInterpolationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rieszInterpolationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rieszInterpolationEncodeBHist h

def rieszInterpolationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rieszInterpolationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rieszInterpolationDecodeBHist tail)

private theorem rieszInterpolation_decode_encode_bhist :
    ∀ h : BHist, rieszInterpolationDecodeBHist (rieszInterpolationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rieszInterpolationFields : RieszInterpolationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RieszInterpolationUp.mk G L P A B W H C S N => [G, L, P, A, B, W, H, C, S, N]

def rieszInterpolationToEventFlow : RieszInterpolationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (rieszInterpolationFields x).map rieszInterpolationEncodeBHist

private def rieszInterpolationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => rieszInterpolationEventAtDefault index rest

def rieszInterpolationFromEventFlow (ef : EventFlow) : Option RieszInterpolationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RieszInterpolationUp.mk
      (rieszInterpolationDecodeBHist (rieszInterpolationEventAtDefault 0 ef))
      (rieszInterpolationDecodeBHist (rieszInterpolationEventAtDefault 1 ef))
      (rieszInterpolationDecodeBHist (rieszInterpolationEventAtDefault 2 ef))
      (rieszInterpolationDecodeBHist (rieszInterpolationEventAtDefault 3 ef))
      (rieszInterpolationDecodeBHist (rieszInterpolationEventAtDefault 4 ef))
      (rieszInterpolationDecodeBHist (rieszInterpolationEventAtDefault 5 ef))
      (rieszInterpolationDecodeBHist (rieszInterpolationEventAtDefault 6 ef))
      (rieszInterpolationDecodeBHist (rieszInterpolationEventAtDefault 7 ef))
      (rieszInterpolationDecodeBHist (rieszInterpolationEventAtDefault 8 ef))
      (rieszInterpolationDecodeBHist (rieszInterpolationEventAtDefault 9 ef)))

private theorem rieszInterpolation_round_trip :
    ∀ x : RieszInterpolationUp,
      rieszInterpolationFromEventFlow (rieszInterpolationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G L P A B W H C S N =>
      change
        some
          (RieszInterpolationUp.mk
            (rieszInterpolationDecodeBHist (rieszInterpolationEncodeBHist G))
            (rieszInterpolationDecodeBHist (rieszInterpolationEncodeBHist L))
            (rieszInterpolationDecodeBHist (rieszInterpolationEncodeBHist P))
            (rieszInterpolationDecodeBHist (rieszInterpolationEncodeBHist A))
            (rieszInterpolationDecodeBHist (rieszInterpolationEncodeBHist B))
            (rieszInterpolationDecodeBHist (rieszInterpolationEncodeBHist W))
            (rieszInterpolationDecodeBHist (rieszInterpolationEncodeBHist H))
            (rieszInterpolationDecodeBHist (rieszInterpolationEncodeBHist C))
            (rieszInterpolationDecodeBHist (rieszInterpolationEncodeBHist S))
            (rieszInterpolationDecodeBHist (rieszInterpolationEncodeBHist N))) =
          some (RieszInterpolationUp.mk G L P A B W H C S N)
      rw [rieszInterpolation_decode_encode_bhist G, rieszInterpolation_decode_encode_bhist L,
        rieszInterpolation_decode_encode_bhist P, rieszInterpolation_decode_encode_bhist A,
        rieszInterpolation_decode_encode_bhist B, rieszInterpolation_decode_encode_bhist W,
        rieszInterpolation_decode_encode_bhist H, rieszInterpolation_decode_encode_bhist C,
        rieszInterpolation_decode_encode_bhist S, rieszInterpolation_decode_encode_bhist N]

private theorem rieszInterpolationToEventFlow_injective {x y : RieszInterpolationUp} :
    rieszInterpolationToEventFlow x = rieszInterpolationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = rieszInterpolationFromEventFlow (rieszInterpolationToEventFlow x) :=
        (rieszInterpolation_round_trip x).symm
      _ = rieszInterpolationFromEventFlow (rieszInterpolationToEventFlow y) :=
        congrArg rieszInterpolationFromEventFlow hxy
      _ = some y := rieszInterpolation_round_trip y
  exact Option.some.inj optionEq

private theorem rieszInterpolation_fields_faithful :
    ∀ x y : RieszInterpolationUp, rieszInterpolationFields x = rieszInterpolationFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk G1 L1 P1 A1 B1 W1 H1 C1 S1 N1 =>
      cases y with
      | mk G2 L2 P2 A2 B2 W2 H2 C2 S2 N2 =>
          cases hfields
          rfl

instance rieszInterpolationBHistCarrier : BHistCarrier RieszInterpolationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rieszInterpolationToEventFlow
  fromEventFlow := rieszInterpolationFromEventFlow

instance rieszInterpolationChapterTasteGate : ChapterTasteGate RieszInterpolationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rieszInterpolationFromEventFlow (rieszInterpolationToEventFlow x) = some x
    exact rieszInterpolation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (rieszInterpolationToEventFlow_injective heq)

instance rieszInterpolationFieldFaithful : FieldFaithful RieszInterpolationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := rieszInterpolationFields
  field_faithful := rieszInterpolation_fields_faithful

instance rieszInterpolationNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RieszInterpolationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RieszInterpolationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RieszInterpolationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RieszInterpolationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RieszInterpolationUp) ∧
      Nonempty (FieldFaithful RieszInterpolationUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RieszInterpolationUp) ∧
          (∀ h : BHist,
            rieszInterpolationDecodeBHist (rieszInterpolationEncodeBHist h) = h) ∧
            (∀ x : RieszInterpolationUp,
              rieszInterpolationFromEventFlow (rieszInterpolationToEventFlow x) = some x) ∧
              rieszInterpolationEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨rieszInterpolationChapterTasteGate⟩,
      ⟨rieszInterpolationFieldFaithful⟩,
      ⟨rieszInterpolationNontrivial⟩,
      rieszInterpolation_decode_encode_bhist,
      rieszInterpolation_round_trip,
      rfl⟩

end BEDC.Derived.RieszInterpolationUp
