import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EmptyBoundarySelectorLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EmptyBoundarySelectorLedgerUp : Type where
  | mk (H M R X S L T C P N : BHist) : EmptyBoundarySelectorLedgerUp
  deriving DecidableEq

def emptyBoundarySelectorLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: emptyBoundarySelectorLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: emptyBoundarySelectorLedgerEncodeBHist h

def emptyBoundarySelectorLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (emptyBoundarySelectorLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (emptyBoundarySelectorLedgerDecodeBHist tail)

theorem EmptyBoundarySelectorLedgerTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      emptyBoundarySelectorLedgerDecodeBHist (emptyBoundarySelectorLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def emptyBoundarySelectorLedgerFields : EmptyBoundarySelectorLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EmptyBoundarySelectorLedgerUp.mk H M R X S L T C P N => [H, M, R, X, S, L, T, C, P, N]

def emptyBoundarySelectorLedgerToEventFlow : EmptyBoundarySelectorLedgerUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | EmptyBoundarySelectorLedgerUp.mk H M R X S L T C P N =>
      [emptyBoundarySelectorLedgerEncodeBHist H, emptyBoundarySelectorLedgerEncodeBHist M,
        emptyBoundarySelectorLedgerEncodeBHist R, emptyBoundarySelectorLedgerEncodeBHist X,
        emptyBoundarySelectorLedgerEncodeBHist S, emptyBoundarySelectorLedgerEncodeBHist L,
        emptyBoundarySelectorLedgerEncodeBHist T, emptyBoundarySelectorLedgerEncodeBHist C,
        emptyBoundarySelectorLedgerEncodeBHist P, emptyBoundarySelectorLedgerEncodeBHist N]

def emptyBoundarySelectorLedgerEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => emptyBoundarySelectorLedgerEventAtDefault index rest

def emptyBoundarySelectorLedgerFromEventFlow (ef : EventFlow) :
    Option EmptyBoundarySelectorLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EmptyBoundarySelectorLedgerUp.mk
      (emptyBoundarySelectorLedgerDecodeBHist (emptyBoundarySelectorLedgerEventAtDefault 0 ef))
      (emptyBoundarySelectorLedgerDecodeBHist (emptyBoundarySelectorLedgerEventAtDefault 1 ef))
      (emptyBoundarySelectorLedgerDecodeBHist (emptyBoundarySelectorLedgerEventAtDefault 2 ef))
      (emptyBoundarySelectorLedgerDecodeBHist (emptyBoundarySelectorLedgerEventAtDefault 3 ef))
      (emptyBoundarySelectorLedgerDecodeBHist (emptyBoundarySelectorLedgerEventAtDefault 4 ef))
      (emptyBoundarySelectorLedgerDecodeBHist (emptyBoundarySelectorLedgerEventAtDefault 5 ef))
      (emptyBoundarySelectorLedgerDecodeBHist (emptyBoundarySelectorLedgerEventAtDefault 6 ef))
      (emptyBoundarySelectorLedgerDecodeBHist (emptyBoundarySelectorLedgerEventAtDefault 7 ef))
      (emptyBoundarySelectorLedgerDecodeBHist (emptyBoundarySelectorLedgerEventAtDefault 8 ef))
      (emptyBoundarySelectorLedgerDecodeBHist (emptyBoundarySelectorLedgerEventAtDefault 9 ef)))

theorem EmptyBoundarySelectorLedgerTasteGate_single_carrier_alignment_round_trip :
    ∀ x : EmptyBoundarySelectorLedgerUp,
      emptyBoundarySelectorLedgerFromEventFlow (emptyBoundarySelectorLedgerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk H M R X S L T C P N =>
      change
        some
          (EmptyBoundarySelectorLedgerUp.mk
            (emptyBoundarySelectorLedgerDecodeBHist (emptyBoundarySelectorLedgerEncodeBHist H))
            (emptyBoundarySelectorLedgerDecodeBHist (emptyBoundarySelectorLedgerEncodeBHist M))
            (emptyBoundarySelectorLedgerDecodeBHist (emptyBoundarySelectorLedgerEncodeBHist R))
            (emptyBoundarySelectorLedgerDecodeBHist (emptyBoundarySelectorLedgerEncodeBHist X))
            (emptyBoundarySelectorLedgerDecodeBHist (emptyBoundarySelectorLedgerEncodeBHist S))
            (emptyBoundarySelectorLedgerDecodeBHist (emptyBoundarySelectorLedgerEncodeBHist L))
            (emptyBoundarySelectorLedgerDecodeBHist (emptyBoundarySelectorLedgerEncodeBHist T))
            (emptyBoundarySelectorLedgerDecodeBHist (emptyBoundarySelectorLedgerEncodeBHist C))
            (emptyBoundarySelectorLedgerDecodeBHist (emptyBoundarySelectorLedgerEncodeBHist P))
            (emptyBoundarySelectorLedgerDecodeBHist (emptyBoundarySelectorLedgerEncodeBHist N))) =
          some (EmptyBoundarySelectorLedgerUp.mk H M R X S L T C P N)
      rw [EmptyBoundarySelectorLedgerTasteGate_single_carrier_alignment_decode_encode H,
        EmptyBoundarySelectorLedgerTasteGate_single_carrier_alignment_decode_encode M,
        EmptyBoundarySelectorLedgerTasteGate_single_carrier_alignment_decode_encode R,
        EmptyBoundarySelectorLedgerTasteGate_single_carrier_alignment_decode_encode X,
        EmptyBoundarySelectorLedgerTasteGate_single_carrier_alignment_decode_encode S,
        EmptyBoundarySelectorLedgerTasteGate_single_carrier_alignment_decode_encode L,
        EmptyBoundarySelectorLedgerTasteGate_single_carrier_alignment_decode_encode T,
        EmptyBoundarySelectorLedgerTasteGate_single_carrier_alignment_decode_encode C,
        EmptyBoundarySelectorLedgerTasteGate_single_carrier_alignment_decode_encode P,
        EmptyBoundarySelectorLedgerTasteGate_single_carrier_alignment_decode_encode N]

theorem EmptyBoundarySelectorLedgerTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : EmptyBoundarySelectorLedgerUp} :
    emptyBoundarySelectorLedgerToEventFlow x = emptyBoundarySelectorLedgerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hread :
      emptyBoundarySelectorLedgerFromEventFlow (emptyBoundarySelectorLedgerToEventFlow x) =
        emptyBoundarySelectorLedgerFromEventFlow (emptyBoundarySelectorLedgerToEventFlow y) :=
    congrArg emptyBoundarySelectorLedgerFromEventFlow hxy
  exact Option.some.inj
    (Eq.trans (EmptyBoundarySelectorLedgerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (EmptyBoundarySelectorLedgerTasteGate_single_carrier_alignment_round_trip y)))

theorem EmptyBoundarySelectorLedgerTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : EmptyBoundarySelectorLedgerUp,
      emptyBoundarySelectorLedgerFields x = emptyBoundarySelectorLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk H₁ M₁ R₁ X₁ S₁ L₁ T₁ C₁ P₁ N₁ =>
      cases y with
      | mk H₂ M₂ R₂ X₂ S₂ L₂ T₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance emptyBoundarySelectorLedgerBHistCarrier :
    BHistCarrier EmptyBoundarySelectorLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := emptyBoundarySelectorLedgerToEventFlow
  fromEventFlow := emptyBoundarySelectorLedgerFromEventFlow

instance emptyBoundarySelectorLedgerChapterTasteGate :
    ChapterTasteGate EmptyBoundarySelectorLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      emptyBoundarySelectorLedgerFromEventFlow (emptyBoundarySelectorLedgerToEventFlow x) =
        some x
    exact EmptyBoundarySelectorLedgerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (EmptyBoundarySelectorLedgerTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance emptyBoundarySelectorLedgerFieldFaithful :
    FieldFaithful EmptyBoundarySelectorLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := emptyBoundarySelectorLedgerFields
  field_faithful :=
    EmptyBoundarySelectorLedgerTasteGate_single_carrier_alignment_field_faithful

instance emptyBoundarySelectorLedgerNontrivial :
    Nontrivial EmptyBoundarySelectorLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EmptyBoundarySelectorLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      EmptyBoundarySelectorLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem EmptyBoundarySelectorLedgerTasteGate_single_carrier_alignment :
    (∀ H M R X S L T C P N : BHist,
      emptyBoundarySelectorLedgerFields
          (EmptyBoundarySelectorLedgerUp.mk H M R X S L T C P N) =
        [H, M, R, X, S, L, T, C, P, N]) ∧
      (∀ h : BHist,
        emptyBoundarySelectorLedgerDecodeBHist (emptyBoundarySelectorLedgerEncodeBHist h) =
          h) ∧
        (∀ x : EmptyBoundarySelectorLedgerUp,
          emptyBoundarySelectorLedgerFromEventFlow
              (emptyBoundarySelectorLedgerToEventFlow x) =
            some x) ∧
          (∀ x y : EmptyBoundarySelectorLedgerUp,
            emptyBoundarySelectorLedgerToEventFlow x =
                emptyBoundarySelectorLedgerToEventFlow y ->
              x = y) ∧
            emptyBoundarySelectorLedgerEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨(fun _ _ _ _ _ _ _ _ _ _ => rfl),
      EmptyBoundarySelectorLedgerTasteGate_single_carrier_alignment_decode_encode,
      EmptyBoundarySelectorLedgerTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        EmptyBoundarySelectorLedgerTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.EmptyBoundarySelectorLedgerUp
