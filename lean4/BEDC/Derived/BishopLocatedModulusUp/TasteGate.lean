import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopLocatedModulusUp : Type where
  | mk :
      (located modulus streamWindow regularReadback dyadicTolerance realSeal transport replay
        provenance localCert : BHist) →
      BishopLocatedModulusUp
  deriving DecidableEq

def bishopLocatedModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedModulusEncodeBHist h

def bishopLocatedModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedModulusDecodeBHist tail)

theorem BishopLocatedModulusTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, bishopLocatedModulusDecodeBHist (bishopLocatedModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopLocatedModulusFields : BishopLocatedModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedModulusUp.mk located modulus streamWindow regularReadback dyadicTolerance
      realSeal transport replay provenance localCert =>
      [located, modulus, streamWindow, regularReadback, dyadicTolerance, realSeal, transport,
        replay, provenance, localCert]

def bishopLocatedModulusToEventFlow : BishopLocatedModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map bishopLocatedModulusEncodeBHist (bishopLocatedModulusFields x)

private def BishopLocatedModulusTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      BishopLocatedModulusTasteGate_single_carrier_alignment_eventAtDefault index rest

def bishopLocatedModulusFromEventFlow : EventFlow → Option BishopLocatedModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (BishopLocatedModulusUp.mk
        (bishopLocatedModulusDecodeBHist
          (BishopLocatedModulusTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
        (bishopLocatedModulusDecodeBHist
          (BishopLocatedModulusTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
        (bishopLocatedModulusDecodeBHist
          (BishopLocatedModulusTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
        (bishopLocatedModulusDecodeBHist
          (BishopLocatedModulusTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
        (bishopLocatedModulusDecodeBHist
          (BishopLocatedModulusTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
        (bishopLocatedModulusDecodeBHist
          (BishopLocatedModulusTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
        (bishopLocatedModulusDecodeBHist
          (BishopLocatedModulusTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
        (bishopLocatedModulusDecodeBHist
          (BishopLocatedModulusTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
        (bishopLocatedModulusDecodeBHist
          (BishopLocatedModulusTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
        (bishopLocatedModulusDecodeBHist
          (BishopLocatedModulusTasteGate_single_carrier_alignment_eventAtDefault 9 ef)))

theorem BishopLocatedModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopLocatedModulusUp,
      bishopLocatedModulusFromEventFlow (bishopLocatedModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk located modulus streamWindow regularReadback dyadicTolerance realSeal transport replay
      provenance localCert =>
      change
        some
          (BishopLocatedModulusUp.mk
            (bishopLocatedModulusDecodeBHist (bishopLocatedModulusEncodeBHist located))
            (bishopLocatedModulusDecodeBHist (bishopLocatedModulusEncodeBHist modulus))
            (bishopLocatedModulusDecodeBHist (bishopLocatedModulusEncodeBHist streamWindow))
            (bishopLocatedModulusDecodeBHist (bishopLocatedModulusEncodeBHist regularReadback))
            (bishopLocatedModulusDecodeBHist (bishopLocatedModulusEncodeBHist dyadicTolerance))
            (bishopLocatedModulusDecodeBHist (bishopLocatedModulusEncodeBHist realSeal))
            (bishopLocatedModulusDecodeBHist (bishopLocatedModulusEncodeBHist transport))
            (bishopLocatedModulusDecodeBHist (bishopLocatedModulusEncodeBHist replay))
            (bishopLocatedModulusDecodeBHist (bishopLocatedModulusEncodeBHist provenance))
            (bishopLocatedModulusDecodeBHist (bishopLocatedModulusEncodeBHist localCert))) =
          some
            (BishopLocatedModulusUp.mk located modulus streamWindow regularReadback
              dyadicTolerance realSeal transport replay provenance localCert)
      rw [BishopLocatedModulusTasteGate_single_carrier_alignment_decode_encode located,
        BishopLocatedModulusTasteGate_single_carrier_alignment_decode_encode modulus,
        BishopLocatedModulusTasteGate_single_carrier_alignment_decode_encode streamWindow,
        BishopLocatedModulusTasteGate_single_carrier_alignment_decode_encode regularReadback,
        BishopLocatedModulusTasteGate_single_carrier_alignment_decode_encode dyadicTolerance,
        BishopLocatedModulusTasteGate_single_carrier_alignment_decode_encode realSeal,
        BishopLocatedModulusTasteGate_single_carrier_alignment_decode_encode transport,
        BishopLocatedModulusTasteGate_single_carrier_alignment_decode_encode replay,
        BishopLocatedModulusTasteGate_single_carrier_alignment_decode_encode provenance,
        BishopLocatedModulusTasteGate_single_carrier_alignment_decode_encode localCert]

theorem BishopLocatedModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopLocatedModulusUp} :
    bishopLocatedModulusToEventFlow x = bishopLocatedModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopLocatedModulusFromEventFlow (bishopLocatedModulusToEventFlow x) =
        bishopLocatedModulusFromEventFlow (bishopLocatedModulusToEventFlow y) :=
    congrArg bishopLocatedModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopLocatedModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BishopLocatedModulusTasteGate_single_carrier_alignment_round_trip y)))

private theorem bishopLocatedModulus_field_faithful :
    ∀ x y : BishopLocatedModulusUp,
      bishopLocatedModulusFields x = bishopLocatedModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk located₁ modulus₁ streamWindow₁ regularReadback₁ dyadicTolerance₁ realSeal₁ transport₁
      replay₁ provenance₁ localCert₁ =>
      cases y with
      | mk located₂ modulus₂ streamWindow₂ regularReadback₂ dyadicTolerance₂ realSeal₂ transport₂
          replay₂ provenance₂ localCert₂ =>
          cases h
          rfl

instance bishopLocatedModulusBHistCarrier : BHistCarrier BishopLocatedModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopLocatedModulusToEventFlow
  fromEventFlow := bishopLocatedModulusFromEventFlow

instance bishopLocatedModulusChapterTasteGate : ChapterTasteGate BishopLocatedModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopLocatedModulusFromEventFlow (bishopLocatedModulusToEventFlow x) = some x
    exact BishopLocatedModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopLocatedModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance bishopLocatedModulusFieldFaithful : FieldFaithful BishopLocatedModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopLocatedModulusFields
  field_faithful := bishopLocatedModulus_field_faithful

instance bishopLocatedModulusNontrivial : Nontrivial BishopLocatedModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopLocatedModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopLocatedModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopLocatedModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopLocatedModulusChapterTasteGate

theorem BishopLocatedModulusTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BishopLocatedModulusUp) ∧
      Nonempty (FieldFaithful BishopLocatedModulusUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial BishopLocatedModulusUp) ∧
      (∀ h : BHist,
        bishopLocatedModulusDecodeBHist (bishopLocatedModulusEncodeBHist h) = h) ∧
      (∀ x : BishopLocatedModulusUp,
        bishopLocatedModulusFromEventFlow (bishopLocatedModulusToEventFlow x) = some x) ∧
      (∀ x y : BishopLocatedModulusUp,
        bishopLocatedModulusToEventFlow x = bishopLocatedModulusToEventFlow y → x = y) ∧
      bishopLocatedModulusEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact Nonempty.intro bishopLocatedModulusChapterTasteGate
  · constructor
    · exact Nonempty.intro bishopLocatedModulusFieldFaithful
    · constructor
      · exact Nonempty.intro bishopLocatedModulusNontrivial
      · constructor
        · exact BishopLocatedModulusTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact BishopLocatedModulusTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact BishopLocatedModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

end BEDC.Derived.BishopLocatedModulusUp
