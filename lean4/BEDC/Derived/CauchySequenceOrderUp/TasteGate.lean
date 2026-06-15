import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySequenceOrderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySequenceOrderUp : Type where
  | mk (X Y A W D L Q R S H C P N : BHist) : CauchySequenceOrderUp
  deriving DecidableEq

def cauchySequenceOrderEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySequenceOrderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySequenceOrderEncodeBHist h

def cauchySequenceOrderDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySequenceOrderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySequenceOrderDecodeBHist tail)

private theorem CauchySequenceOrderTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchySequenceOrderDecodeBHist (cauchySequenceOrderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchySequenceOrderFields : CauchySequenceOrderUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySequenceOrderUp.mk X Y A W D L Q R S H C P N => [X, Y, A, W, D, L, Q, R, S, H, C, P, N]

def cauchySequenceOrderToEventFlow : CauchySequenceOrderUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchySequenceOrderFields x).map cauchySequenceOrderEncodeBHist

private def cauchySequenceOrderEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchySequenceOrderEventAt index rest

def cauchySequenceOrderFromEventFlow (ef : EventFlow) :
    Option CauchySequenceOrderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchySequenceOrderUp.mk
      (cauchySequenceOrderDecodeBHist (cauchySequenceOrderEventAt 0 ef))
      (cauchySequenceOrderDecodeBHist (cauchySequenceOrderEventAt 1 ef))
      (cauchySequenceOrderDecodeBHist (cauchySequenceOrderEventAt 2 ef))
      (cauchySequenceOrderDecodeBHist (cauchySequenceOrderEventAt 3 ef))
      (cauchySequenceOrderDecodeBHist (cauchySequenceOrderEventAt 4 ef))
      (cauchySequenceOrderDecodeBHist (cauchySequenceOrderEventAt 5 ef))
      (cauchySequenceOrderDecodeBHist (cauchySequenceOrderEventAt 6 ef))
      (cauchySequenceOrderDecodeBHist (cauchySequenceOrderEventAt 7 ef))
      (cauchySequenceOrderDecodeBHist (cauchySequenceOrderEventAt 8 ef))
      (cauchySequenceOrderDecodeBHist (cauchySequenceOrderEventAt 9 ef))
      (cauchySequenceOrderDecodeBHist (cauchySequenceOrderEventAt 10 ef))
      (cauchySequenceOrderDecodeBHist (cauchySequenceOrderEventAt 11 ef))
      (cauchySequenceOrderDecodeBHist (cauchySequenceOrderEventAt 12 ef)))

private theorem CauchySequenceOrderTasteGate_single_carrier_alignment_round_trip
    (x : CauchySequenceOrderUp) :
    cauchySequenceOrderFromEventFlow (cauchySequenceOrderToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X Y A W D L Q R S H C P N =>
      change
        some
          (CauchySequenceOrderUp.mk
            (cauchySequenceOrderDecodeBHist (cauchySequenceOrderEncodeBHist X))
            (cauchySequenceOrderDecodeBHist (cauchySequenceOrderEncodeBHist Y))
            (cauchySequenceOrderDecodeBHist (cauchySequenceOrderEncodeBHist A))
            (cauchySequenceOrderDecodeBHist (cauchySequenceOrderEncodeBHist W))
            (cauchySequenceOrderDecodeBHist (cauchySequenceOrderEncodeBHist D))
            (cauchySequenceOrderDecodeBHist (cauchySequenceOrderEncodeBHist L))
            (cauchySequenceOrderDecodeBHist (cauchySequenceOrderEncodeBHist Q))
            (cauchySequenceOrderDecodeBHist (cauchySequenceOrderEncodeBHist R))
            (cauchySequenceOrderDecodeBHist (cauchySequenceOrderEncodeBHist S))
            (cauchySequenceOrderDecodeBHist (cauchySequenceOrderEncodeBHist H))
            (cauchySequenceOrderDecodeBHist (cauchySequenceOrderEncodeBHist C))
            (cauchySequenceOrderDecodeBHist (cauchySequenceOrderEncodeBHist P))
            (cauchySequenceOrderDecodeBHist (cauchySequenceOrderEncodeBHist N))) =
          some (CauchySequenceOrderUp.mk X Y A W D L Q R S H C P N)
      rw [CauchySequenceOrderTasteGate_single_carrier_alignment_decode_encode X,
        CauchySequenceOrderTasteGate_single_carrier_alignment_decode_encode Y,
        CauchySequenceOrderTasteGate_single_carrier_alignment_decode_encode A,
        CauchySequenceOrderTasteGate_single_carrier_alignment_decode_encode W,
        CauchySequenceOrderTasteGate_single_carrier_alignment_decode_encode D,
        CauchySequenceOrderTasteGate_single_carrier_alignment_decode_encode L,
        CauchySequenceOrderTasteGate_single_carrier_alignment_decode_encode Q,
        CauchySequenceOrderTasteGate_single_carrier_alignment_decode_encode R,
        CauchySequenceOrderTasteGate_single_carrier_alignment_decode_encode S,
        CauchySequenceOrderTasteGate_single_carrier_alignment_decode_encode H,
        CauchySequenceOrderTasteGate_single_carrier_alignment_decode_encode C,
        CauchySequenceOrderTasteGate_single_carrier_alignment_decode_encode P,
        CauchySequenceOrderTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchySequenceOrderTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchySequenceOrderUp} :
    cauchySequenceOrderToEventFlow x = cauchySequenceOrderToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySequenceOrderFromEventFlow (cauchySequenceOrderToEventFlow x) =
        cauchySequenceOrderFromEventFlow (cauchySequenceOrderToEventFlow y) :=
    congrArg cauchySequenceOrderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchySequenceOrderTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchySequenceOrderTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchySequenceOrderTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchySequenceOrderUp, cauchySequenceOrderFields x = cauchySequenceOrderFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ Y₁ A₁ W₁ D₁ L₁ Q₁ R₁ S₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ Y₂ A₂ W₂ D₂ L₂ Q₂ R₂ S₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchySequenceOrderBHistCarrier : BHistCarrier CauchySequenceOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySequenceOrderToEventFlow
  fromEventFlow := cauchySequenceOrderFromEventFlow

instance cauchySequenceOrderChapterTasteGate : ChapterTasteGate CauchySequenceOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchySequenceOrderFromEventFlow (cauchySequenceOrderToEventFlow x) = some x
    exact CauchySequenceOrderTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchySequenceOrderTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchySequenceOrderFieldFaithful : FieldFaithful CauchySequenceOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchySequenceOrderFields
  field_faithful := CauchySequenceOrderTasteGate_single_carrier_alignment_fields_faithful

theorem CauchySequenceOrderTasteGate_single_carrier_alignment :
    (forall h : BHist, cauchySequenceOrderDecodeBHist (cauchySequenceOrderEncodeBHist h) = h) ∧
      (forall x : CauchySequenceOrderUp, cauchySequenceOrderFromEventFlow (cauchySequenceOrderToEventFlow x) = some x) ∧
        (forall x y : CauchySequenceOrderUp, cauchySequenceOrderToEventFlow x = cauchySequenceOrderToEventFlow y -> x = y) ∧
          cauchySequenceOrderEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨CauchySequenceOrderTasteGate_single_carrier_alignment_decode_encode,
      CauchySequenceOrderTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchySequenceOrderTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchySequenceOrderUp
