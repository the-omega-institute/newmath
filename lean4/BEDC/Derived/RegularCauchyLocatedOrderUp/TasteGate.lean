import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyLocatedOrderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyLocatedOrderUp : Type where
  | mk (L R W D Q E H C P N : BHist) : RegularCauchyLocatedOrderUp
  deriving DecidableEq

def regularCauchyLocatedOrderEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyLocatedOrderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyLocatedOrderEncodeBHist h

def regularCauchyLocatedOrderDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyLocatedOrderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyLocatedOrderDecodeBHist tail)

private theorem regularCauchyLocatedOrderDecode_encode :
    ∀ h : BHist,
      regularCauchyLocatedOrderDecodeBHist (regularCauchyLocatedOrderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyLocatedOrderFields : RegularCauchyLocatedOrderUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyLocatedOrderUp.mk L R W D Q E H C P N => [L, R, W, D, Q, E, H, C, P, N]

def regularCauchyLocatedOrderToEventFlow : RegularCauchyLocatedOrderUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map regularCauchyLocatedOrderEncodeBHist (regularCauchyLocatedOrderFields x)

private def regularCauchyLocatedOrderEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyLocatedOrderEventAtDefault index rest

def regularCauchyLocatedOrderFromEventFlow :
    EventFlow → Option RegularCauchyLocatedOrderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RegularCauchyLocatedOrderUp.mk
        (regularCauchyLocatedOrderDecodeBHist (regularCauchyLocatedOrderEventAtDefault 0 ef))
        (regularCauchyLocatedOrderDecodeBHist (regularCauchyLocatedOrderEventAtDefault 1 ef))
        (regularCauchyLocatedOrderDecodeBHist (regularCauchyLocatedOrderEventAtDefault 2 ef))
        (regularCauchyLocatedOrderDecodeBHist (regularCauchyLocatedOrderEventAtDefault 3 ef))
        (regularCauchyLocatedOrderDecodeBHist (regularCauchyLocatedOrderEventAtDefault 4 ef))
        (regularCauchyLocatedOrderDecodeBHist (regularCauchyLocatedOrderEventAtDefault 5 ef))
        (regularCauchyLocatedOrderDecodeBHist (regularCauchyLocatedOrderEventAtDefault 6 ef))
        (regularCauchyLocatedOrderDecodeBHist (regularCauchyLocatedOrderEventAtDefault 7 ef))
        (regularCauchyLocatedOrderDecodeBHist (regularCauchyLocatedOrderEventAtDefault 8 ef))
        (regularCauchyLocatedOrderDecodeBHist (regularCauchyLocatedOrderEventAtDefault 9 ef)))

private theorem regularCauchyLocatedOrder_round_trip :
    ∀ x : RegularCauchyLocatedOrderUp,
      regularCauchyLocatedOrderFromEventFlow (regularCauchyLocatedOrderToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L R W D Q E H C P N =>
      change
        some
          (RegularCauchyLocatedOrderUp.mk
            (regularCauchyLocatedOrderDecodeBHist (regularCauchyLocatedOrderEncodeBHist L))
            (regularCauchyLocatedOrderDecodeBHist (regularCauchyLocatedOrderEncodeBHist R))
            (regularCauchyLocatedOrderDecodeBHist (regularCauchyLocatedOrderEncodeBHist W))
            (regularCauchyLocatedOrderDecodeBHist (regularCauchyLocatedOrderEncodeBHist D))
            (regularCauchyLocatedOrderDecodeBHist (regularCauchyLocatedOrderEncodeBHist Q))
            (regularCauchyLocatedOrderDecodeBHist (regularCauchyLocatedOrderEncodeBHist E))
            (regularCauchyLocatedOrderDecodeBHist (regularCauchyLocatedOrderEncodeBHist H))
            (regularCauchyLocatedOrderDecodeBHist (regularCauchyLocatedOrderEncodeBHist C))
            (regularCauchyLocatedOrderDecodeBHist (regularCauchyLocatedOrderEncodeBHist P))
            (regularCauchyLocatedOrderDecodeBHist (regularCauchyLocatedOrderEncodeBHist N))) =
          some (RegularCauchyLocatedOrderUp.mk L R W D Q E H C P N)
      rw [regularCauchyLocatedOrderDecode_encode L, regularCauchyLocatedOrderDecode_encode R,
        regularCauchyLocatedOrderDecode_encode W, regularCauchyLocatedOrderDecode_encode D,
        regularCauchyLocatedOrderDecode_encode Q, regularCauchyLocatedOrderDecode_encode E,
        regularCauchyLocatedOrderDecode_encode H, regularCauchyLocatedOrderDecode_encode C,
        regularCauchyLocatedOrderDecode_encode P, regularCauchyLocatedOrderDecode_encode N]

private theorem regularCauchyLocatedOrderToEventFlow_injective
    {x y : RegularCauchyLocatedOrderUp} :
    regularCauchyLocatedOrderToEventFlow x = regularCauchyLocatedOrderToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyLocatedOrderFromEventFlow (regularCauchyLocatedOrderToEventFlow x) =
        regularCauchyLocatedOrderFromEventFlow (regularCauchyLocatedOrderToEventFlow y) :=
    congrArg regularCauchyLocatedOrderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyLocatedOrder_round_trip x).symm
      (Eq.trans hread (regularCauchyLocatedOrder_round_trip y)))

private theorem regularCauchyLocatedOrder_field_faithful :
    ∀ x y : RegularCauchyLocatedOrderUp,
      regularCauchyLocatedOrderFields x = regularCauchyLocatedOrderFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk L₁ R₁ W₁ D₁ Q₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk L₂ R₂ W₂ D₂ Q₂ E₂ H₂ C₂ P₂ N₂ =>
          cases h
          rfl

instance regularCauchyLocatedOrderBHistCarrier :
    BHistCarrier RegularCauchyLocatedOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyLocatedOrderToEventFlow
  fromEventFlow := regularCauchyLocatedOrderFromEventFlow

instance regularCauchyLocatedOrderChapterTasteGate :
    ChapterTasteGate RegularCauchyLocatedOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyLocatedOrderFromEventFlow (regularCauchyLocatedOrderToEventFlow x) =
        some x
    exact regularCauchyLocatedOrder_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyLocatedOrderToEventFlow_injective heq)

instance regularCauchyLocatedOrderFieldFaithful :
    FieldFaithful RegularCauchyLocatedOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyLocatedOrderFields
  field_faithful := regularCauchyLocatedOrder_field_faithful

def taste_gate : ChapterTasteGate RegularCauchyLocatedOrderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyLocatedOrderChapterTasteGate

theorem RegularCauchyLocatedOrderUp_single_carrier_alignment :
    (∀ h : BHist,
        regularCauchyLocatedOrderDecodeBHist (regularCauchyLocatedOrderEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyLocatedOrderUp,
        regularCauchyLocatedOrderFromEventFlow (regularCauchyLocatedOrderToEventFlow x) =
          some x) ∧
      (∀ x y : RegularCauchyLocatedOrderUp,
        regularCauchyLocatedOrderToEventFlow x = regularCauchyLocatedOrderToEventFlow y →
          x = y) ∧
      regularCauchyLocatedOrderEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨regularCauchyLocatedOrderDecode_encode,
      regularCauchyLocatedOrder_round_trip,
      (fun _ _ heq => regularCauchyLocatedOrderToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyLocatedOrderUp
