import BEDC.Derived.MonotoneBarModulusUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MonotoneBarModulusUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def monotoneBarModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: monotoneBarModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: monotoneBarModulusEncodeBHist h

def monotoneBarModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (monotoneBarModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (monotoneBarModulusDecodeBHist tail)

private theorem monotoneBarModulus_decode_encode_bhist :
    ∀ h : BHist, monotoneBarModulusDecodeBHist (monotoneBarModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def monotoneBarModulusFields : BEDC.Derived.MonotoneBarModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.MonotoneBarModulusUp.mk T B D W R E H C P N =>
      [T, B, D, W, R, E, H, C, P, N]

def monotoneBarModulusToEventFlow : BEDC.Derived.MonotoneBarModulusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (monotoneBarModulusFields x).map monotoneBarModulusEncodeBHist

private def monotoneBarModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => monotoneBarModulusEventAtDefault index rest

def monotoneBarModulusFromEventFlow
    (ef : EventFlow) : Option BEDC.Derived.MonotoneBarModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BEDC.Derived.MonotoneBarModulusUp.mk
      (monotoneBarModulusDecodeBHist (monotoneBarModulusEventAtDefault 0 ef))
      (monotoneBarModulusDecodeBHist (monotoneBarModulusEventAtDefault 1 ef))
      (monotoneBarModulusDecodeBHist (monotoneBarModulusEventAtDefault 2 ef))
      (monotoneBarModulusDecodeBHist (monotoneBarModulusEventAtDefault 3 ef))
      (monotoneBarModulusDecodeBHist (monotoneBarModulusEventAtDefault 4 ef))
      (monotoneBarModulusDecodeBHist (monotoneBarModulusEventAtDefault 5 ef))
      (monotoneBarModulusDecodeBHist (monotoneBarModulusEventAtDefault 6 ef))
      (monotoneBarModulusDecodeBHist (monotoneBarModulusEventAtDefault 7 ef))
      (monotoneBarModulusDecodeBHist (monotoneBarModulusEventAtDefault 8 ef))
      (monotoneBarModulusDecodeBHist (monotoneBarModulusEventAtDefault 9 ef)))

private theorem monotoneBarModulus_round_trip :
    ∀ x : BEDC.Derived.MonotoneBarModulusUp,
      monotoneBarModulusFromEventFlow (monotoneBarModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T B D W R E H C P N =>
      change
        some
          (BEDC.Derived.MonotoneBarModulusUp.mk
            (monotoneBarModulusDecodeBHist (monotoneBarModulusEncodeBHist T))
            (monotoneBarModulusDecodeBHist (monotoneBarModulusEncodeBHist B))
            (monotoneBarModulusDecodeBHist (monotoneBarModulusEncodeBHist D))
            (monotoneBarModulusDecodeBHist (monotoneBarModulusEncodeBHist W))
            (monotoneBarModulusDecodeBHist (monotoneBarModulusEncodeBHist R))
            (monotoneBarModulusDecodeBHist (monotoneBarModulusEncodeBHist E))
            (monotoneBarModulusDecodeBHist (monotoneBarModulusEncodeBHist H))
            (monotoneBarModulusDecodeBHist (monotoneBarModulusEncodeBHist C))
            (monotoneBarModulusDecodeBHist (monotoneBarModulusEncodeBHist P))
            (monotoneBarModulusDecodeBHist (monotoneBarModulusEncodeBHist N))) =
          some (BEDC.Derived.MonotoneBarModulusUp.mk T B D W R E H C P N)
      rw [monotoneBarModulus_decode_encode_bhist T,
        monotoneBarModulus_decode_encode_bhist B,
        monotoneBarModulus_decode_encode_bhist D,
        monotoneBarModulus_decode_encode_bhist W,
        monotoneBarModulus_decode_encode_bhist R,
        monotoneBarModulus_decode_encode_bhist E,
        monotoneBarModulus_decode_encode_bhist H,
        monotoneBarModulus_decode_encode_bhist C,
        monotoneBarModulus_decode_encode_bhist P,
        monotoneBarModulus_decode_encode_bhist N]

private theorem monotoneBarModulusToEventFlow_injective
    {x y : BEDC.Derived.MonotoneBarModulusUp} :
    monotoneBarModulusToEventFlow x = monotoneBarModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      monotoneBarModulusFromEventFlow (monotoneBarModulusToEventFlow x) =
        monotoneBarModulusFromEventFlow (monotoneBarModulusToEventFlow y) :=
    congrArg monotoneBarModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (monotoneBarModulus_round_trip x).symm
      (Eq.trans hread (monotoneBarModulus_round_trip y)))

private theorem monotoneBarModulus_fields_faithful :
    ∀ x y : BEDC.Derived.MonotoneBarModulusUp,
      monotoneBarModulusFields x = monotoneBarModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 B1 D1 W1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk T2 B2 D2 W2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance monotoneBarModulusBHistCarrier :
    BHistCarrier BEDC.Derived.MonotoneBarModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := monotoneBarModulusToEventFlow
  fromEventFlow := monotoneBarModulusFromEventFlow

instance monotoneBarModulusChapterTasteGate :
    ChapterTasteGate BEDC.Derived.MonotoneBarModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change monotoneBarModulusFromEventFlow (monotoneBarModulusToEventFlow x) = some x
    exact monotoneBarModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (monotoneBarModulusToEventFlow_injective heq)

instance monotoneBarModulusFieldFaithful :
    FieldFaithful BEDC.Derived.MonotoneBarModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := monotoneBarModulusFields
  field_faithful := monotoneBarModulus_fields_faithful

instance monotoneBarModulusNontrivial : Nontrivial BEDC.Derived.MonotoneBarModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BEDC.Derived.MonotoneBarModulusUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BEDC.Derived.MonotoneBarModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BEDC.Derived.MonotoneBarModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  monotoneBarModulusChapterTasteGate

theorem MonotoneBarModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist, monotoneBarModulusDecodeBHist (monotoneBarModulusEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BEDC.Derived.MonotoneBarModulusUp) ∧
        Nonempty (ChapterTasteGate BEDC.Derived.MonotoneBarModulusUp) ∧
          Nonempty (FieldFaithful BEDC.Derived.MonotoneBarModulusUp) ∧
            Nonempty (Nontrivial BEDC.Derived.MonotoneBarModulusUp) ∧
              monotoneBarModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨monotoneBarModulus_decode_encode_bhist, ⟨monotoneBarModulusBHistCarrier⟩,
      ⟨monotoneBarModulusChapterTasteGate⟩, ⟨monotoneBarModulusFieldFaithful⟩,
      ⟨monotoneBarModulusNontrivial⟩, rfl⟩

end BEDC.Derived.MonotoneBarModulusUp.TasteGate
