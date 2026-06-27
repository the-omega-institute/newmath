import BEDC.Derived.CompactDiniModulusUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactDiniModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def compactDiniModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactDiniModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactDiniModulusEncodeBHist h

def compactDiniModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactDiniModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactDiniModulusDecodeBHist tail)

private theorem compactDiniModulus_decode_encode_bhist :
    ∀ h : BHist, compactDiniModulusDecodeBHist (compactDiniModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactDiniModulusFields : BEDC.Derived.CompactDiniModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactDiniModulusUp.mk K F M epsilon L U R E H C P N =>
      [K, F, M, epsilon, L, U, R, E, H, C, P, N]

def compactDiniModulusToEventFlow : BEDC.Derived.CompactDiniModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactDiniModulusFields x).map compactDiniModulusEncodeBHist

private def compactDiniModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactDiniModulusEventAtDefault index rest

def compactDiniModulusFromEventFlow
    (ef : EventFlow) : Option BEDC.Derived.CompactDiniModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactDiniModulusUp.mk
      (compactDiniModulusDecodeBHist (compactDiniModulusEventAtDefault 0 ef))
      (compactDiniModulusDecodeBHist (compactDiniModulusEventAtDefault 1 ef))
      (compactDiniModulusDecodeBHist (compactDiniModulusEventAtDefault 2 ef))
      (compactDiniModulusDecodeBHist (compactDiniModulusEventAtDefault 3 ef))
      (compactDiniModulusDecodeBHist (compactDiniModulusEventAtDefault 4 ef))
      (compactDiniModulusDecodeBHist (compactDiniModulusEventAtDefault 5 ef))
      (compactDiniModulusDecodeBHist (compactDiniModulusEventAtDefault 6 ef))
      (compactDiniModulusDecodeBHist (compactDiniModulusEventAtDefault 7 ef))
      (compactDiniModulusDecodeBHist (compactDiniModulusEventAtDefault 8 ef))
      (compactDiniModulusDecodeBHist (compactDiniModulusEventAtDefault 9 ef))
      (compactDiniModulusDecodeBHist (compactDiniModulusEventAtDefault 10 ef))
      (compactDiniModulusDecodeBHist (compactDiniModulusEventAtDefault 11 ef)))

private theorem compactDiniModulus_round_trip
    (x : BEDC.Derived.CompactDiniModulusUp) :
    compactDiniModulusFromEventFlow (compactDiniModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K F M epsilon L U R E H C P N =>
      change
        some
          (CompactDiniModulusUp.mk
            (compactDiniModulusDecodeBHist (compactDiniModulusEncodeBHist K))
            (compactDiniModulusDecodeBHist (compactDiniModulusEncodeBHist F))
            (compactDiniModulusDecodeBHist (compactDiniModulusEncodeBHist M))
            (compactDiniModulusDecodeBHist (compactDiniModulusEncodeBHist epsilon))
            (compactDiniModulusDecodeBHist (compactDiniModulusEncodeBHist L))
            (compactDiniModulusDecodeBHist (compactDiniModulusEncodeBHist U))
            (compactDiniModulusDecodeBHist (compactDiniModulusEncodeBHist R))
            (compactDiniModulusDecodeBHist (compactDiniModulusEncodeBHist E))
            (compactDiniModulusDecodeBHist (compactDiniModulusEncodeBHist H))
            (compactDiniModulusDecodeBHist (compactDiniModulusEncodeBHist C))
            (compactDiniModulusDecodeBHist (compactDiniModulusEncodeBHist P))
            (compactDiniModulusDecodeBHist (compactDiniModulusEncodeBHist N))) =
          some (CompactDiniModulusUp.mk K F M epsilon L U R E H C P N)
      rw [compactDiniModulus_decode_encode_bhist K,
        compactDiniModulus_decode_encode_bhist F,
        compactDiniModulus_decode_encode_bhist M,
        compactDiniModulus_decode_encode_bhist epsilon,
        compactDiniModulus_decode_encode_bhist L,
        compactDiniModulus_decode_encode_bhist U,
        compactDiniModulus_decode_encode_bhist R,
        compactDiniModulus_decode_encode_bhist E,
        compactDiniModulus_decode_encode_bhist H,
        compactDiniModulus_decode_encode_bhist C,
        compactDiniModulus_decode_encode_bhist P,
        compactDiniModulus_decode_encode_bhist N]

private theorem compactDiniModulusToEventFlow_injective
    {x y : BEDC.Derived.CompactDiniModulusUp} :
    compactDiniModulusToEventFlow x = compactDiniModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactDiniModulusFromEventFlow (compactDiniModulusToEventFlow x) =
        compactDiniModulusFromEventFlow (compactDiniModulusToEventFlow y) :=
    congrArg compactDiniModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactDiniModulus_round_trip x).symm
      (Eq.trans hread (compactDiniModulus_round_trip y)))

private theorem compactDiniModulus_fields_faithful :
    ∀ x y : BEDC.Derived.CompactDiniModulusUp,
      compactDiniModulusFields x = compactDiniModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ F₁ M₁ epsilon₁ L₁ U₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ F₂ M₂ epsilon₂ L₂ U₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance compactDiniModulusBHistCarrier :
    BHistCarrier BEDC.Derived.CompactDiniModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactDiniModulusToEventFlow
  fromEventFlow := compactDiniModulusFromEventFlow

instance compactDiniModulusChapterTasteGate :
    ChapterTasteGate BEDC.Derived.CompactDiniModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactDiniModulusFromEventFlow (compactDiniModulusToEventFlow x) = some x
    exact compactDiniModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactDiniModulusToEventFlow_injective heq)

instance compactDiniModulusFieldFaithful :
    FieldFaithful BEDC.Derived.CompactDiniModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactDiniModulusFields
  field_faithful := compactDiniModulus_fields_faithful

instance compactDiniModulusNontrivial :
    Nontrivial BEDC.Derived.CompactDiniModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactDiniModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      CompactDiniModulusUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CompactDiniModulusTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier BEDC.Derived.CompactDiniModulusUp) ∧
      Nonempty (ChapterTasteGate BEDC.Derived.CompactDiniModulusUp) ∧
        compactDiniModulusEncodeBHist BHist.Empty = ([] : RawEvent) ∧
          compactDiniModulusDecodeBHist [BMark.b1] = BHist.e1 BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨⟨compactDiniModulusBHistCarrier⟩,
      ⟨⟨compactDiniModulusChapterTasteGate⟩,
        rfl,
        rfl⟩⟩

end BEDC.Derived.CompactDiniModulusUp
