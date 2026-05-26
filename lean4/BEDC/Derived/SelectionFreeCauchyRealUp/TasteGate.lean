import BEDC.Derived.SelectionFreeCauchyRealUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SelectionFreeCauchyRealUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def selectionFreeCauchyRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: selectionFreeCauchyRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: selectionFreeCauchyRealEncodeBHist h

def selectionFreeCauchyRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (selectionFreeCauchyRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (selectionFreeCauchyRealDecodeBHist tail)

private theorem SelectionFreeCauchyRealTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      selectionFreeCauchyRealDecodeBHist (selectionFreeCauchyRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def selectionFreeCauchyRealFields : BEDC.Derived.SelectionFreeCauchyRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.SelectionFreeCauchyRealUp.mk S R D Q E B H C P N =>
      [S, R, D, Q, E, B, H, C, P, N]

def selectionFreeCauchyRealToEventFlow : BEDC.Derived.SelectionFreeCauchyRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.SelectionFreeCauchyRealUp.mk S R D Q E B H C P N =>
      [selectionFreeCauchyRealEncodeBHist S,
        selectionFreeCauchyRealEncodeBHist R,
        selectionFreeCauchyRealEncodeBHist D,
        selectionFreeCauchyRealEncodeBHist Q,
        selectionFreeCauchyRealEncodeBHist E,
        selectionFreeCauchyRealEncodeBHist B,
        selectionFreeCauchyRealEncodeBHist H,
        selectionFreeCauchyRealEncodeBHist C,
        selectionFreeCauchyRealEncodeBHist P,
        selectionFreeCauchyRealEncodeBHist N]

private def selectionFreeCauchyRealEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => selectionFreeCauchyRealEventAtDefault index rest

def selectionFreeCauchyRealFromEventFlow
    (ef : EventFlow) : Option BEDC.Derived.SelectionFreeCauchyRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BEDC.Derived.SelectionFreeCauchyRealUp.mk
      (selectionFreeCauchyRealDecodeBHist (selectionFreeCauchyRealEventAtDefault 0 ef))
      (selectionFreeCauchyRealDecodeBHist (selectionFreeCauchyRealEventAtDefault 1 ef))
      (selectionFreeCauchyRealDecodeBHist (selectionFreeCauchyRealEventAtDefault 2 ef))
      (selectionFreeCauchyRealDecodeBHist (selectionFreeCauchyRealEventAtDefault 3 ef))
      (selectionFreeCauchyRealDecodeBHist (selectionFreeCauchyRealEventAtDefault 4 ef))
      (selectionFreeCauchyRealDecodeBHist (selectionFreeCauchyRealEventAtDefault 5 ef))
      (selectionFreeCauchyRealDecodeBHist (selectionFreeCauchyRealEventAtDefault 6 ef))
      (selectionFreeCauchyRealDecodeBHist (selectionFreeCauchyRealEventAtDefault 7 ef))
      (selectionFreeCauchyRealDecodeBHist (selectionFreeCauchyRealEventAtDefault 8 ef))
      (selectionFreeCauchyRealDecodeBHist (selectionFreeCauchyRealEventAtDefault 9 ef)))

private theorem SelectionFreeCauchyRealTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BEDC.Derived.SelectionFreeCauchyRealUp,
      selectionFreeCauchyRealFromEventFlow (selectionFreeCauchyRealToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R D Q E B H C P N =>
      change
        some
          (BEDC.Derived.SelectionFreeCauchyRealUp.mk
            (selectionFreeCauchyRealDecodeBHist (selectionFreeCauchyRealEncodeBHist S))
            (selectionFreeCauchyRealDecodeBHist (selectionFreeCauchyRealEncodeBHist R))
            (selectionFreeCauchyRealDecodeBHist (selectionFreeCauchyRealEncodeBHist D))
            (selectionFreeCauchyRealDecodeBHist (selectionFreeCauchyRealEncodeBHist Q))
            (selectionFreeCauchyRealDecodeBHist (selectionFreeCauchyRealEncodeBHist E))
            (selectionFreeCauchyRealDecodeBHist (selectionFreeCauchyRealEncodeBHist B))
            (selectionFreeCauchyRealDecodeBHist (selectionFreeCauchyRealEncodeBHist H))
            (selectionFreeCauchyRealDecodeBHist (selectionFreeCauchyRealEncodeBHist C))
            (selectionFreeCauchyRealDecodeBHist (selectionFreeCauchyRealEncodeBHist P))
            (selectionFreeCauchyRealDecodeBHist (selectionFreeCauchyRealEncodeBHist N))) =
          some (BEDC.Derived.SelectionFreeCauchyRealUp.mk S R D Q E B H C P N)
      rw [SelectionFreeCauchyRealTasteGate_single_carrier_alignment_decode S,
        SelectionFreeCauchyRealTasteGate_single_carrier_alignment_decode R,
        SelectionFreeCauchyRealTasteGate_single_carrier_alignment_decode D,
        SelectionFreeCauchyRealTasteGate_single_carrier_alignment_decode Q,
        SelectionFreeCauchyRealTasteGate_single_carrier_alignment_decode E,
        SelectionFreeCauchyRealTasteGate_single_carrier_alignment_decode B,
        SelectionFreeCauchyRealTasteGate_single_carrier_alignment_decode H,
        SelectionFreeCauchyRealTasteGate_single_carrier_alignment_decode C,
        SelectionFreeCauchyRealTasteGate_single_carrier_alignment_decode P,
        SelectionFreeCauchyRealTasteGate_single_carrier_alignment_decode N]

private theorem SelectionFreeCauchyRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BEDC.Derived.SelectionFreeCauchyRealUp} :
    selectionFreeCauchyRealToEventFlow x = selectionFreeCauchyRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      selectionFreeCauchyRealFromEventFlow (selectionFreeCauchyRealToEventFlow x) =
        selectionFreeCauchyRealFromEventFlow (selectionFreeCauchyRealToEventFlow y) :=
    congrArg selectionFreeCauchyRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SelectionFreeCauchyRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SelectionFreeCauchyRealTasteGate_single_carrier_alignment_round_trip y)))

private theorem SelectionFreeCauchyRealTasteGate_single_carrier_alignment_fields :
    ∀ x y : BEDC.Derived.SelectionFreeCauchyRealUp,
      selectionFreeCauchyRealFields x = selectionFreeCauchyRealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 R1 D1 Q1 E1 B1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 R2 D2 Q2 E2 B2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance selectionFreeCauchyRealBHistCarrier :
    BHistCarrier BEDC.Derived.SelectionFreeCauchyRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := selectionFreeCauchyRealToEventFlow
  fromEventFlow := selectionFreeCauchyRealFromEventFlow

instance selectionFreeCauchyRealChapterTasteGate :
    ChapterTasteGate BEDC.Derived.SelectionFreeCauchyRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := SelectionFreeCauchyRealTasteGate_single_carrier_alignment_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SelectionFreeCauchyRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance selectionFreeCauchyRealFieldFaithful :
    FieldFaithful BEDC.Derived.SelectionFreeCauchyRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := selectionFreeCauchyRealFields
  field_faithful := SelectionFreeCauchyRealTasteGate_single_carrier_alignment_fields

instance selectionFreeCauchyRealNontrivial :
    Nontrivial BEDC.Derived.SelectionFreeCauchyRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BEDC.Derived.SelectionFreeCauchyRealUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      BEDC.Derived.SelectionFreeCauchyRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BEDC.Derived.SelectionFreeCauchyRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  selectionFreeCauchyRealChapterTasteGate

theorem SelectionFreeCauchyRealTasteGate_single_carrier_alignment :
    (∀ h : BHist, selectionFreeCauchyRealDecodeBHist
      (selectionFreeCauchyRealEncodeBHist h) = h) ∧
      (∀ x : BEDC.Derived.SelectionFreeCauchyRealUp,
        selectionFreeCauchyRealFromEventFlow (selectionFreeCauchyRealToEventFlow x) =
          some x) ∧
        (∀ x y : BEDC.Derived.SelectionFreeCauchyRealUp,
          selectionFreeCauchyRealToEventFlow x = selectionFreeCauchyRealToEventFlow y →
            x = y) ∧
          selectionFreeCauchyRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨SelectionFreeCauchyRealTasteGate_single_carrier_alignment_decode,
      SelectionFreeCauchyRealTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        SelectionFreeCauchyRealTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SelectionFreeCauchyRealUp.TasteGate
