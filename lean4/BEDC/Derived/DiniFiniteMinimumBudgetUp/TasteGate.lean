import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiniFiniteMinimumBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiniFiniteMinimumBudgetUp : Type where
  | mk (K F D U Q E H C P N : BHist) : DiniFiniteMinimumBudgetUp
  deriving DecidableEq

def diniFiniteMinimumBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: diniFiniteMinimumBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: diniFiniteMinimumBudgetEncodeBHist h

def diniFiniteMinimumBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (diniFiniteMinimumBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (diniFiniteMinimumBudgetDecodeBHist tail)

private theorem DiniFiniteMinimumBudgetTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def diniFiniteMinimumBudgetFields : DiniFiniteMinimumBudgetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DiniFiniteMinimumBudgetUp.mk K F D U Q E H C P N => [K, F, D, U, Q, E, H, C, P, N]

def diniFiniteMinimumBudgetToEventFlow : DiniFiniteMinimumBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (diniFiniteMinimumBudgetFields x).map diniFiniteMinimumBudgetEncodeBHist

private def diniFiniteMinimumBudgetEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => diniFiniteMinimumBudgetEventAtDefault index rest

def diniFiniteMinimumBudgetFromEventFlow
    (ef : EventFlow) : Option DiniFiniteMinimumBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DiniFiniteMinimumBudgetUp.mk
      (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEventAtDefault 0 ef))
      (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEventAtDefault 1 ef))
      (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEventAtDefault 2 ef))
      (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEventAtDefault 3 ef))
      (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEventAtDefault 4 ef))
      (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEventAtDefault 5 ef))
      (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEventAtDefault 6 ef))
      (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEventAtDefault 7 ef))
      (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEventAtDefault 8 ef))
      (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEventAtDefault 9 ef)))

private theorem DiniFiniteMinimumBudgetTasteGate_single_carrier_alignment_round_trip
    (x : DiniFiniteMinimumBudgetUp) :
    diniFiniteMinimumBudgetFromEventFlow (diniFiniteMinimumBudgetToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K F D U Q E H C P N =>
      change
        some
          (DiniFiniteMinimumBudgetUp.mk
            (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEncodeBHist K))
            (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEncodeBHist F))
            (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEncodeBHist D))
            (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEncodeBHist U))
            (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEncodeBHist Q))
            (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEncodeBHist E))
            (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEncodeBHist H))
            (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEncodeBHist C))
            (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEncodeBHist P))
            (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEncodeBHist N))) =
          some (DiniFiniteMinimumBudgetUp.mk K F D U Q E H C P N)
      rw [DiniFiniteMinimumBudgetTasteGate_single_carrier_alignment_decode_encode K,
        DiniFiniteMinimumBudgetTasteGate_single_carrier_alignment_decode_encode F,
        DiniFiniteMinimumBudgetTasteGate_single_carrier_alignment_decode_encode D,
        DiniFiniteMinimumBudgetTasteGate_single_carrier_alignment_decode_encode U,
        DiniFiniteMinimumBudgetTasteGate_single_carrier_alignment_decode_encode Q,
        DiniFiniteMinimumBudgetTasteGate_single_carrier_alignment_decode_encode E,
        DiniFiniteMinimumBudgetTasteGate_single_carrier_alignment_decode_encode H,
        DiniFiniteMinimumBudgetTasteGate_single_carrier_alignment_decode_encode C,
        DiniFiniteMinimumBudgetTasteGate_single_carrier_alignment_decode_encode P,
        DiniFiniteMinimumBudgetTasteGate_single_carrier_alignment_decode_encode N]

private theorem DiniFiniteMinimumBudgetTasteGate_single_carrier_alignment_injective
    {x y : DiniFiniteMinimumBudgetUp} :
    diniFiniteMinimumBudgetToEventFlow x = diniFiniteMinimumBudgetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      diniFiniteMinimumBudgetFromEventFlow (diniFiniteMinimumBudgetToEventFlow x) =
        diniFiniteMinimumBudgetFromEventFlow (diniFiniteMinimumBudgetToEventFlow y) :=
    congrArg diniFiniteMinimumBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DiniFiniteMinimumBudgetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DiniFiniteMinimumBudgetTasteGate_single_carrier_alignment_round_trip y)))

private theorem DiniFiniteMinimumBudgetTasteGate_single_carrier_alignment_fields :
    ∀ x y : DiniFiniteMinimumBudgetUp,
      diniFiniteMinimumBudgetFields x = diniFiniteMinimumBudgetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ F₁ D₁ U₁ Q₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ F₂ D₂ U₂ Q₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance diniFiniteMinimumBudgetBHistCarrier :
    BHistCarrier DiniFiniteMinimumBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := diniFiniteMinimumBudgetToEventFlow
  fromEventFlow := diniFiniteMinimumBudgetFromEventFlow

instance diniFiniteMinimumBudgetChapterTasteGate :
    ChapterTasteGate DiniFiniteMinimumBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change diniFiniteMinimumBudgetFromEventFlow (diniFiniteMinimumBudgetToEventFlow x) =
      some x
    exact DiniFiniteMinimumBudgetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DiniFiniteMinimumBudgetTasteGate_single_carrier_alignment_injective heq)

instance diniFiniteMinimumBudgetFieldFaithful :
    FieldFaithful DiniFiniteMinimumBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := diniFiniteMinimumBudgetFields
  field_faithful := DiniFiniteMinimumBudgetTasteGate_single_carrier_alignment_fields

instance diniFiniteMinimumBudgetNontrivial : Nontrivial DiniFiniteMinimumBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DiniFiniteMinimumBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      DiniFiniteMinimumBudgetUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem DiniFiniteMinimumBudgetTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEncodeBHist h) = h) ∧
      (∀ x : DiniFiniteMinimumBudgetUp,
        diniFiniteMinimumBudgetFromEventFlow (diniFiniteMinimumBudgetToEventFlow x) =
          some x) ∧
        (∀ x y : DiniFiniteMinimumBudgetUp,
          diniFiniteMinimumBudgetToEventFlow x =
            diniFiniteMinimumBudgetToEventFlow y → x = y) ∧
          diniFiniteMinimumBudgetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨DiniFiniteMinimumBudgetTasteGate_single_carrier_alignment_decode_encode,
      DiniFiniteMinimumBudgetTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => DiniFiniteMinimumBudgetTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.DiniFiniteMinimumBudgetUp
