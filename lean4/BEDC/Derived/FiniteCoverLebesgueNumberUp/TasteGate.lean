import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteCoverLebesgueNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteCoverLebesgueNumberUp : Type where
  | mk (K M V R L U H C P N : BHist) : FiniteCoverLebesgueNumberUp
  deriving DecidableEq

def finiteCoverLebesgueNumberEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteCoverLebesgueNumberEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteCoverLebesgueNumberEncodeBHist h

def finiteCoverLebesgueNumberDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteCoverLebesgueNumberDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteCoverLebesgueNumberDecodeBHist tail)

private theorem FiniteCoverLebesgueNumberTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      finiteCoverLebesgueNumberDecodeBHist (finiteCoverLebesgueNumberEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteCoverLebesgueNumberFields : FiniteCoverLebesgueNumberUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteCoverLebesgueNumberUp.mk K M V R L U H C P N =>
      [K, M, V, R, L, U, H, C, P, N]

def finiteCoverLebesgueNumberToEventFlow : FiniteCoverLebesgueNumberUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteCoverLebesgueNumberFields x).map finiteCoverLebesgueNumberEncodeBHist

private def finiteCoverLebesgueNumberEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteCoverLebesgueNumberEventAt index rest

def finiteCoverLebesgueNumberFromEventFlow (ef : EventFlow) :
    Option FiniteCoverLebesgueNumberUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteCoverLebesgueNumberUp.mk
      (finiteCoverLebesgueNumberDecodeBHist (finiteCoverLebesgueNumberEventAt 0 ef))
      (finiteCoverLebesgueNumberDecodeBHist (finiteCoverLebesgueNumberEventAt 1 ef))
      (finiteCoverLebesgueNumberDecodeBHist (finiteCoverLebesgueNumberEventAt 2 ef))
      (finiteCoverLebesgueNumberDecodeBHist (finiteCoverLebesgueNumberEventAt 3 ef))
      (finiteCoverLebesgueNumberDecodeBHist (finiteCoverLebesgueNumberEventAt 4 ef))
      (finiteCoverLebesgueNumberDecodeBHist (finiteCoverLebesgueNumberEventAt 5 ef))
      (finiteCoverLebesgueNumberDecodeBHist (finiteCoverLebesgueNumberEventAt 6 ef))
      (finiteCoverLebesgueNumberDecodeBHist (finiteCoverLebesgueNumberEventAt 7 ef))
      (finiteCoverLebesgueNumberDecodeBHist (finiteCoverLebesgueNumberEventAt 8 ef))
      (finiteCoverLebesgueNumberDecodeBHist (finiteCoverLebesgueNumberEventAt 9 ef)))

private theorem FiniteCoverLebesgueNumberTasteGate_single_carrier_alignment_round_trip
    (x : FiniteCoverLebesgueNumberUp) :
    finiteCoverLebesgueNumberFromEventFlow (finiteCoverLebesgueNumberToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K M V R L U H C P N =>
      change
        some
          (FiniteCoverLebesgueNumberUp.mk
            (finiteCoverLebesgueNumberDecodeBHist (finiteCoverLebesgueNumberEncodeBHist K))
            (finiteCoverLebesgueNumberDecodeBHist (finiteCoverLebesgueNumberEncodeBHist M))
            (finiteCoverLebesgueNumberDecodeBHist (finiteCoverLebesgueNumberEncodeBHist V))
            (finiteCoverLebesgueNumberDecodeBHist (finiteCoverLebesgueNumberEncodeBHist R))
            (finiteCoverLebesgueNumberDecodeBHist (finiteCoverLebesgueNumberEncodeBHist L))
            (finiteCoverLebesgueNumberDecodeBHist (finiteCoverLebesgueNumberEncodeBHist U))
            (finiteCoverLebesgueNumberDecodeBHist (finiteCoverLebesgueNumberEncodeBHist H))
            (finiteCoverLebesgueNumberDecodeBHist (finiteCoverLebesgueNumberEncodeBHist C))
            (finiteCoverLebesgueNumberDecodeBHist (finiteCoverLebesgueNumberEncodeBHist P))
            (finiteCoverLebesgueNumberDecodeBHist (finiteCoverLebesgueNumberEncodeBHist N))) =
          some (FiniteCoverLebesgueNumberUp.mk K M V R L U H C P N)
      rw [FiniteCoverLebesgueNumberTasteGate_single_carrier_alignment_decode_encode K,
        FiniteCoverLebesgueNumberTasteGate_single_carrier_alignment_decode_encode M,
        FiniteCoverLebesgueNumberTasteGate_single_carrier_alignment_decode_encode V,
        FiniteCoverLebesgueNumberTasteGate_single_carrier_alignment_decode_encode R,
        FiniteCoverLebesgueNumberTasteGate_single_carrier_alignment_decode_encode L,
        FiniteCoverLebesgueNumberTasteGate_single_carrier_alignment_decode_encode U,
        FiniteCoverLebesgueNumberTasteGate_single_carrier_alignment_decode_encode H,
        FiniteCoverLebesgueNumberTasteGate_single_carrier_alignment_decode_encode C,
        FiniteCoverLebesgueNumberTasteGate_single_carrier_alignment_decode_encode P,
        FiniteCoverLebesgueNumberTasteGate_single_carrier_alignment_decode_encode N]

private theorem FiniteCoverLebesgueNumberTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteCoverLebesgueNumberUp} :
    finiteCoverLebesgueNumberToEventFlow x = finiteCoverLebesgueNumberToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteCoverLebesgueNumberFromEventFlow (finiteCoverLebesgueNumberToEventFlow x) =
        finiteCoverLebesgueNumberFromEventFlow (finiteCoverLebesgueNumberToEventFlow y) :=
    congrArg finiteCoverLebesgueNumberFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteCoverLebesgueNumberTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteCoverLebesgueNumberTasteGate_single_carrier_alignment_round_trip y)))

private theorem FiniteCoverLebesgueNumberTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : FiniteCoverLebesgueNumberUp,
      finiteCoverLebesgueNumberFields x = finiteCoverLebesgueNumberFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ M₁ V₁ R₁ L₁ U₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ M₂ V₂ R₂ L₂ U₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance finiteCoverLebesgueNumberBHistCarrier :
    BHistCarrier FiniteCoverLebesgueNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteCoverLebesgueNumberToEventFlow
  fromEventFlow := finiteCoverLebesgueNumberFromEventFlow

instance finiteCoverLebesgueNumberChapterTasteGate :
    ChapterTasteGate FiniteCoverLebesgueNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteCoverLebesgueNumberFromEventFlow
      (finiteCoverLebesgueNumberToEventFlow x) = some x
    exact FiniteCoverLebesgueNumberTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (FiniteCoverLebesgueNumberTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance finiteCoverLebesgueNumberFieldFaithful :
    FieldFaithful FiniteCoverLebesgueNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteCoverLebesgueNumberFields
  field_faithful :=
    FiniteCoverLebesgueNumberTasteGate_single_carrier_alignment_fields_faithful

instance finiteCoverLebesgueNumberNontrivial : Nontrivial FiniteCoverLebesgueNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteCoverLebesgueNumberUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteCoverLebesgueNumberUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def FiniteCoverLebesgueNumberTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate FiniteCoverLebesgueNumberUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteCoverLebesgueNumberChapterTasteGate

theorem FiniteCoverLebesgueNumberTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteCoverLebesgueNumberDecodeBHist (finiteCoverLebesgueNumberEncodeBHist h) = h) ∧
      (∀ x : FiniteCoverLebesgueNumberUp,
        finiteCoverLebesgueNumberFromEventFlow (finiteCoverLebesgueNumberToEventFlow x) =
          some x) ∧
      (∀ x y : FiniteCoverLebesgueNumberUp,
        finiteCoverLebesgueNumberToEventFlow x = finiteCoverLebesgueNumberToEventFlow y →
          x = y) ∧
      finiteCoverLebesgueNumberEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FiniteCoverLebesgueNumberTasteGate_single_carrier_alignment_decode_encode,
      FiniteCoverLebesgueNumberTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        FiniteCoverLebesgueNumberTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.FiniteCoverLebesgueNumberUp
