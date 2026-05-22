import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopFanModulusUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopFanModulusUp : Type where
  | mk (F A B S Q D R U H C P N : BHist) : BishopFanModulusUp
  deriving DecidableEq

def bishopFanModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopFanModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopFanModulusEncodeBHist h

def bishopFanModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopFanModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopFanModulusDecodeBHist tail)

private theorem bishopFanModulus_decode_encode_bhist :
    ∀ h : BHist, bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopFanModulusFields : BishopFanModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopFanModulusUp.mk F A B S Q D R U H C P N =>
      [F, A, B, S, Q, D, R, U, H, C, P, N]

def bishopFanModulusToEventFlow : BishopFanModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopFanModulusFields x).map bishopFanModulusEncodeBHist

private def bishopFanModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopFanModulusEventAtDefault index rest

def bishopFanModulusFromEventFlow (ef : EventFlow) : Option BishopFanModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopFanModulusUp.mk
      (bishopFanModulusDecodeBHist (bishopFanModulusEventAtDefault 0 ef))
      (bishopFanModulusDecodeBHist (bishopFanModulusEventAtDefault 1 ef))
      (bishopFanModulusDecodeBHist (bishopFanModulusEventAtDefault 2 ef))
      (bishopFanModulusDecodeBHist (bishopFanModulusEventAtDefault 3 ef))
      (bishopFanModulusDecodeBHist (bishopFanModulusEventAtDefault 4 ef))
      (bishopFanModulusDecodeBHist (bishopFanModulusEventAtDefault 5 ef))
      (bishopFanModulusDecodeBHist (bishopFanModulusEventAtDefault 6 ef))
      (bishopFanModulusDecodeBHist (bishopFanModulusEventAtDefault 7 ef))
      (bishopFanModulusDecodeBHist (bishopFanModulusEventAtDefault 8 ef))
      (bishopFanModulusDecodeBHist (bishopFanModulusEventAtDefault 9 ef))
      (bishopFanModulusDecodeBHist (bishopFanModulusEventAtDefault 10 ef))
      (bishopFanModulusDecodeBHist (bishopFanModulusEventAtDefault 11 ef)))

private theorem bishopFanModulus_round_trip :
    ∀ x : BishopFanModulusUp,
      bishopFanModulusFromEventFlow (bishopFanModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F A B S Q D R U H C P N =>
      change
        some
          (BishopFanModulusUp.mk
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist F))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist A))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist B))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist S))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist Q))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist D))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist R))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist U))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist H))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist C))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist P))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist N))) =
          some (BishopFanModulusUp.mk F A B S Q D R U H C P N)
      rw [bishopFanModulus_decode_encode_bhist F,
        bishopFanModulus_decode_encode_bhist A,
        bishopFanModulus_decode_encode_bhist B,
        bishopFanModulus_decode_encode_bhist S,
        bishopFanModulus_decode_encode_bhist Q,
        bishopFanModulus_decode_encode_bhist D,
        bishopFanModulus_decode_encode_bhist R,
        bishopFanModulus_decode_encode_bhist U,
        bishopFanModulus_decode_encode_bhist H,
        bishopFanModulus_decode_encode_bhist C,
        bishopFanModulus_decode_encode_bhist P,
        bishopFanModulus_decode_encode_bhist N]

private theorem bishopFanModulusToEventFlow_injective {x y : BishopFanModulusUp} :
    bishopFanModulusToEventFlow x = bishopFanModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopFanModulusFromEventFlow (bishopFanModulusToEventFlow x) =
        bishopFanModulusFromEventFlow (bishopFanModulusToEventFlow y) :=
    congrArg bishopFanModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopFanModulus_round_trip x).symm
      (Eq.trans hread (bishopFanModulus_round_trip y)))

private theorem bishopFanModulus_fields_faithful :
    ∀ x y : BishopFanModulusUp, bishopFanModulusFields x = bishopFanModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 A1 B1 S1 Q1 D1 R1 U1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 A2 B2 S2 Q2 D2 R2 U2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bishopFanModulusBHistCarrier : BHistCarrier BishopFanModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopFanModulusToEventFlow
  fromEventFlow := bishopFanModulusFromEventFlow

instance bishopFanModulusChapterTasteGate : ChapterTasteGate BishopFanModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopFanModulusFromEventFlow (bishopFanModulusToEventFlow x) = some x
    exact bishopFanModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopFanModulusToEventFlow_injective heq)

instance bishopFanModulusFieldFaithful : FieldFaithful BishopFanModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopFanModulusFields
  field_faithful := bishopFanModulus_fields_faithful

instance bishopFanModulusNontrivial : Nontrivial BishopFanModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopFanModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopFanModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopFanModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopFanModulusChapterTasteGate

theorem BishopFanModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist h) = h) ∧
      (∀ x : BishopFanModulusUp,
        bishopFanModulusFromEventFlow (bishopFanModulusToEventFlow x) = some x) ∧
        (∀ x y : BishopFanModulusUp,
          bishopFanModulusToEventFlow x = bishopFanModulusToEventFlow y → x = y) ∧
          bishopFanModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨bishopFanModulus_decode_encode_bhist,
      bishopFanModulus_round_trip,
      (fun _ _ heq => bishopFanModulusToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BishopFanModulusUp.TasteGate

namespace BEDC.Derived.BishopFanModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.Derived.BishopFanModulusUp.TasteGate

theorem BishopFanModulusUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist h) = h) ∧
      (∀ x : BishopFanModulusUp,
        bishopFanModulusToEventFlow x =
          List.map bishopFanModulusEncodeBHist (bishopFanModulusFields x)) ∧
        (∀ x y : BishopFanModulusUp, bishopFanModulusFields x = bishopFanModulusFields y →
          x = y) ∧
          (∃ x y : BishopFanModulusUp, x ≠ y) ∧
            bishopFanModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact BishopFanModulusTasteGate_single_carrier_alignment.left
  · constructor
    · intro x
      rfl
    · constructor
      · exact bishopFanModulus_fields_faithful
      · constructor
        · exact
            ⟨BishopFanModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty,
              BishopFanModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty,
              by
                intro h
                cases h⟩
        · rfl

end BEDC.Derived.BishopFanModulusUp
