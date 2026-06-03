import BEDC.Derived.RealLocatedOrderUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealLocatedOrderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def realLocatedOrderEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realLocatedOrderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realLocatedOrderEncodeBHist h

def realLocatedOrderDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realLocatedOrderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realLocatedOrderDecodeBHist tail)

private theorem realLocatedOrder_decode_encode_bhist :
    ∀ h : BHist, realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realLocatedOrderToEventFlow : RealLocatedOrderUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealLocatedOrderUp.mk source Y R S D O A H C P =>
      [realLocatedOrderEncodeBHist source.toBHist, realLocatedOrderEncodeBHist Y,
        realLocatedOrderEncodeBHist R, realLocatedOrderEncodeBHist S,
        realLocatedOrderEncodeBHist D, realLocatedOrderEncodeBHist O,
        realLocatedOrderEncodeBHist A, realLocatedOrderEncodeBHist H,
        realLocatedOrderEncodeBHist C, realLocatedOrderEncodeBHist P,
        realLocatedOrderEncodeBHist source.toBHist]

private def realLocatedOrderEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realLocatedOrderEventAtDefault index rest

private def realLocatedOrderUnaryRowFromBHist : BHist → Option RealLocatedOrderUnaryRow
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => some RealLocatedOrderUnaryRow.empty
  | BHist.e0 _tail => none
  | BHist.e1 tail =>
      match realLocatedOrderUnaryRowFromBHist tail with
      | some row => some (RealLocatedOrderUnaryRow.e1 row)
      | none => none

private theorem realLocatedOrderUnaryRowFromBHist_self (row : RealLocatedOrderUnaryRow) :
    realLocatedOrderUnaryRowFromBHist row.toBHist = some row := by
  -- BEDC touchpoint anchor: BHist BMark UnaryHistory
  induction row with
  | empty =>
      rfl
  | e1 tail ih =>
      change
        (match realLocatedOrderUnaryRowFromBHist tail.toBHist with
          | some row => some (RealLocatedOrderUnaryRow.e1 row)
          | none => none) =
          some (RealLocatedOrderUnaryRow.e1 tail)
      rw [ih]

def realLocatedOrderFromEventFlow (ef : EventFlow) : Option RealLocatedOrderUp :=
  -- BEDC touchpoint anchor: BHist BMark hsame UnaryHistory
  let sourceEvent := realLocatedOrderEventAtDefault 0 ef
  let source := realLocatedOrderDecodeBHist sourceEvent
  let target := realLocatedOrderDecodeBHist (realLocatedOrderEventAtDefault 1 ef)
  let readback := realLocatedOrderDecodeBHist (realLocatedOrderEventAtDefault 2 ef)
  let window := realLocatedOrderDecodeBHist (realLocatedOrderEventAtDefault 3 ef)
  let tolerance := realLocatedOrderDecodeBHist (realLocatedOrderEventAtDefault 4 ef)
  let located := realLocatedOrderDecodeBHist (realLocatedOrderEventAtDefault 5 ef)
  let apartness := realLocatedOrderDecodeBHist (realLocatedOrderEventAtDefault 6 ef)
  let transport := realLocatedOrderDecodeBHist (realLocatedOrderEventAtDefault 7 ef)
  let continuation := realLocatedOrderDecodeBHist (realLocatedOrderEventAtDefault 8 ef)
  let provenance := realLocatedOrderDecodeBHist (realLocatedOrderEventAtDefault 9 ef)
  match realLocatedOrderUnaryRowFromBHist source with
  | none => none
  | some sourceRow =>
      some
        (RealLocatedOrderUp.mk sourceRow target readback window tolerance located apartness
          transport continuation provenance)

private theorem realLocatedOrder_round_trip :
    ∀ x : RealLocatedOrderUp,
      realLocatedOrderFromEventFlow (realLocatedOrderToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark hsame UnaryHistory
  intro token
  cases token with
  | mk source Y R S D O A H C P =>
      change
        (match
            realLocatedOrderUnaryRowFromBHist
              (realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist source.toBHist))
          with
          | none => none
          | some sourceRow =>
              some
                (RealLocatedOrderUp.mk sourceRow
                  (realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist Y))
                  (realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist R))
                  (realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist S))
                  (realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist D))
                  (realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist O))
                  (realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist A))
                  (realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist H))
                  (realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist C))
                  (realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist P)))) =
          some (RealLocatedOrderUp.mk source Y R S D O A H C P)
      rw [realLocatedOrder_decode_encode_bhist source.toBHist,
        realLocatedOrder_decode_encode_bhist Y,
        realLocatedOrder_decode_encode_bhist R,
        realLocatedOrder_decode_encode_bhist S,
        realLocatedOrder_decode_encode_bhist D,
        realLocatedOrder_decode_encode_bhist O,
        realLocatedOrder_decode_encode_bhist A,
        realLocatedOrder_decode_encode_bhist H,
        realLocatedOrder_decode_encode_bhist C,
        realLocatedOrder_decode_encode_bhist P,
        realLocatedOrderUnaryRowFromBHist_self source]

private theorem realLocatedOrderToEventFlow_injective {x y : RealLocatedOrderUp} :
    realLocatedOrderToEventFlow x = realLocatedOrderToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk source₁ Y₁ R₁ S₁ D₁ O₁ A₁ H₁ C₁ P₁ =>
      cases y with
      | mk source₂ Y₂ R₂ S₂ D₂ O₂ A₂ H₂ C₂ P₂ =>
          simp only [realLocatedOrderToEventFlow] at heq
          injection heq with hX t1
          injection t1 with hY t2
          injection t2 with hR t3
          injection t3 with hS t4
          injection t4 with hD t5
          injection t5 with hO t6
          injection t6 with hA t7
          injection t7 with hH t8
          injection t8 with hC t9
          injection t9 with hP t10
          injection t10 with hN _
          have rawX : realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist source₁.toBHist) =
              realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist source₂.toBHist) :=
            congrArg realLocatedOrderDecodeBHist hX
          have rawY : realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist Y₁) =
              realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist Y₂) :=
            congrArg realLocatedOrderDecodeBHist hY
          have rawR : realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist R₁) =
              realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist R₂) :=
            congrArg realLocatedOrderDecodeBHist hR
          have rawS : realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist S₁) =
              realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist S₂) :=
            congrArg realLocatedOrderDecodeBHist hS
          have rawD : realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist D₁) =
              realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist D₂) :=
            congrArg realLocatedOrderDecodeBHist hD
          have rawO : realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist O₁) =
              realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist O₂) :=
            congrArg realLocatedOrderDecodeBHist hO
          have rawA : realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist A₁) =
              realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist A₂) :=
            congrArg realLocatedOrderDecodeBHist hA
          have rawH : realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist H₁) =
              realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist H₂) :=
            congrArg realLocatedOrderDecodeBHist hH
          have rawC : realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist C₁) =
              realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist C₂) :=
            congrArg realLocatedOrderDecodeBHist hC
          have rawP : realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist P₁) =
              realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist P₂) :=
            congrArg realLocatedOrderDecodeBHist hP
          have rawN : realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist source₁.toBHist) =
              realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist source₂.toBHist) :=
            congrArg realLocatedOrderDecodeBHist hN
          rw [realLocatedOrder_decode_encode_bhist source₁.toBHist,
            realLocatedOrder_decode_encode_bhist source₂.toBHist] at rawX
          rw [realLocatedOrder_decode_encode_bhist Y₁,
            realLocatedOrder_decode_encode_bhist Y₂] at rawY
          rw [realLocatedOrder_decode_encode_bhist R₁,
            realLocatedOrder_decode_encode_bhist R₂] at rawR
          rw [realLocatedOrder_decode_encode_bhist S₁,
            realLocatedOrder_decode_encode_bhist S₂] at rawS
          rw [realLocatedOrder_decode_encode_bhist D₁,
            realLocatedOrder_decode_encode_bhist D₂] at rawD
          rw [realLocatedOrder_decode_encode_bhist O₁,
            realLocatedOrder_decode_encode_bhist O₂] at rawO
          rw [realLocatedOrder_decode_encode_bhist A₁,
            realLocatedOrder_decode_encode_bhist A₂] at rawA
          rw [realLocatedOrder_decode_encode_bhist H₁,
            realLocatedOrder_decode_encode_bhist H₂] at rawH
          rw [realLocatedOrder_decode_encode_bhist C₁,
            realLocatedOrder_decode_encode_bhist C₂] at rawC
          rw [realLocatedOrder_decode_encode_bhist P₁,
            realLocatedOrder_decode_encode_bhist P₂] at rawP
          rw [realLocatedOrder_decode_encode_bhist source₁.toBHist,
            realLocatedOrder_decode_encode_bhist source₂.toBHist] at rawN
          have sourceEq : source₁ = source₂ :=
            RealLocatedOrderUnaryRow.toBHist_injective rawX
          cases sourceEq
          cases rawY
          cases rawR
          cases rawS
          cases rawD
          cases rawO
          cases rawA
          cases rawH
          cases rawC
          cases rawP
          cases rawN
          rfl

instance realLocatedOrderBHistCarrier : BHistCarrier RealLocatedOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realLocatedOrderToEventFlow
  fromEventFlow := realLocatedOrderFromEventFlow

instance realLocatedOrderChapterTasteGate : ChapterTasteGate RealLocatedOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realLocatedOrderFromEventFlow (realLocatedOrderToEventFlow x) = some x
    exact realLocatedOrder_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realLocatedOrderToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealLocatedOrderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realLocatedOrderChapterTasteGate

theorem RealLocatedOrderTasteGate_single_carrier_alignment :
    (∀ h : BHist, realLocatedOrderDecodeBHist (realLocatedOrderEncodeBHist h) = h) ∧
      (∀ x : RealLocatedOrderUp,
        realLocatedOrderFromEventFlow (realLocatedOrderToEventFlow x) = some x) ∧
        (∀ x y : RealLocatedOrderUp,
          realLocatedOrderToEventFlow x = realLocatedOrderToEventFlow y → x = y) ∧
          realLocatedOrderEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨realLocatedOrder_decode_encode_bhist,
      realLocatedOrder_round_trip,
      (by
        intro x y heq
        exact realLocatedOrderToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealLocatedOrderUp
