import BEDC.Derived.RegularSequenceBishopUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularSequenceBishopUp

open BEDC.Derived
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def regularSequenceBishopEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularSequenceBishopEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularSequenceBishopEncodeBHist h

def regularSequenceBishopDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularSequenceBishopDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularSequenceBishopDecodeBHist tail)

private theorem RegularSequenceBishopTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, regularSequenceBishopDecodeBHist (regularSequenceBishopEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularSequenceBishopFields : RegularSequenceBishopUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularSequenceBishopUp.mk W D Q R N => [W, D, Q, R, N]

def regularSequenceBishopToEventFlow : RegularSequenceBishopUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regularSequenceBishopFields x).map regularSequenceBishopEncodeBHist

private def regularSequenceBishopEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularSequenceBishopEventAtDefault index rest

def regularSequenceBishopFromEventFlow (ef : EventFlow) : Option RegularSequenceBishopUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularSequenceBishopUp.mk
      (regularSequenceBishopDecodeBHist (regularSequenceBishopEventAtDefault 0 ef))
      (regularSequenceBishopDecodeBHist (regularSequenceBishopEventAtDefault 1 ef))
      (regularSequenceBishopDecodeBHist (regularSequenceBishopEventAtDefault 2 ef))
      (regularSequenceBishopDecodeBHist (regularSequenceBishopEventAtDefault 3 ef))
      (regularSequenceBishopDecodeBHist (regularSequenceBishopEventAtDefault 4 ef)))

private theorem RegularSequenceBishopTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularSequenceBishopUp,
      regularSequenceBishopFromEventFlow (regularSequenceBishopToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W D Q R N =>
      change
        some
          (RegularSequenceBishopUp.mk
            (regularSequenceBishopDecodeBHist (regularSequenceBishopEncodeBHist W))
            (regularSequenceBishopDecodeBHist (regularSequenceBishopEncodeBHist D))
            (regularSequenceBishopDecodeBHist (regularSequenceBishopEncodeBHist Q))
            (regularSequenceBishopDecodeBHist (regularSequenceBishopEncodeBHist R))
            (regularSequenceBishopDecodeBHist (regularSequenceBishopEncodeBHist N))) =
          some (RegularSequenceBishopUp.mk W D Q R N)
      rw [RegularSequenceBishopTasteGate_single_carrier_alignment_decode_encode W,
        RegularSequenceBishopTasteGate_single_carrier_alignment_decode_encode D,
        RegularSequenceBishopTasteGate_single_carrier_alignment_decode_encode Q,
        RegularSequenceBishopTasteGate_single_carrier_alignment_decode_encode R,
        RegularSequenceBishopTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularSequenceBishopTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularSequenceBishopUp} :
    regularSequenceBishopToEventFlow x = regularSequenceBishopToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularSequenceBishopFromEventFlow (regularSequenceBishopToEventFlow x) =
        regularSequenceBishopFromEventFlow (regularSequenceBishopToEventFlow y) :=
    congrArg regularSequenceBishopFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularSequenceBishopTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegularSequenceBishopTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularSequenceBishopTasteGate_single_carrier_alignment_fields :
    ∀ x y : RegularSequenceBishopUp, regularSequenceBishopFields x = regularSequenceBishopFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W1 D1 Q1 R1 N1 =>
      cases y with
      | mk W2 D2 Q2 R2 N2 =>
          cases hfields
          rfl

instance regularSequenceBishopBHistCarrier : BHistCarrier RegularSequenceBishopUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularSequenceBishopToEventFlow
  fromEventFlow := regularSequenceBishopFromEventFlow

instance regularSequenceBishopChapterTasteGate : ChapterTasteGate RegularSequenceBishopUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularSequenceBishopFromEventFlow (regularSequenceBishopToEventFlow x) = some x
    exact RegularSequenceBishopTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularSequenceBishopTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularSequenceBishopFieldFaithful : FieldFaithful RegularSequenceBishopUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularSequenceBishopFields
  field_faithful := RegularSequenceBishopTasteGate_single_carrier_alignment_fields

private def regularSequenceBishopNontrivialDef : Nontrivial RegularSequenceBishopUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularSequenceBishopUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularSequenceBishopUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

instance regularSequenceBishopNontrivial : Nontrivial RegularSequenceBishopUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularSequenceBishopNontrivialDef

theorem RegularSequenceBishopTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularSequenceBishopUp) ∧
      Nonempty (FieldFaithful RegularSequenceBishopUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RegularSequenceBishopUp) ∧
          (∀ h : BHist, regularSequenceBishopDecodeBHist (regularSequenceBishopEncodeBHist h) = h) ∧
            (∀ x : RegularSequenceBishopUp,
              regularSequenceBishopFromEventFlow (regularSequenceBishopToEventFlow x) = some x) ∧
              (∀ x y : RegularSequenceBishopUp,
                regularSequenceBishopToEventFlow x = regularSequenceBishopToEventFlow y → x = y) ∧
                regularSequenceBishopEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨regularSequenceBishopChapterTasteGate⟩,
      ⟨regularSequenceBishopFieldFaithful⟩,
      ⟨regularSequenceBishopNontrivialDef⟩,
      RegularSequenceBishopTasteGate_single_carrier_alignment_decode_encode,
      RegularSequenceBishopTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RegularSequenceBishopTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularSequenceBishopUp
