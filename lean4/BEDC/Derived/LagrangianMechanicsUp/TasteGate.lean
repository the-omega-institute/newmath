import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LagrangianMechanicsUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LagrangianMechanicsUp : Type where
  | mk (Q V A R E G S J H C P N : BHist) : LagrangianMechanicsUp
  deriving DecidableEq

def lagrangianMechanicsEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lagrangianMechanicsEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lagrangianMechanicsEncodeBHist h

def lagrangianMechanicsDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lagrangianMechanicsDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lagrangianMechanicsDecodeBHist tail)

private theorem LagrangianMechanicsTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, lagrangianMechanicsDecodeBHist (lagrangianMechanicsEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lagrangianMechanicsToEventFlow : LagrangianMechanicsUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LagrangianMechanicsUp.mk Q V A R E G S J H C P N =>
      [lagrangianMechanicsEncodeBHist Q,
        lagrangianMechanicsEncodeBHist V,
        lagrangianMechanicsEncodeBHist A,
        lagrangianMechanicsEncodeBHist R,
        lagrangianMechanicsEncodeBHist E,
        lagrangianMechanicsEncodeBHist G,
        lagrangianMechanicsEncodeBHist S,
        lagrangianMechanicsEncodeBHist J,
        lagrangianMechanicsEncodeBHist H,
        lagrangianMechanicsEncodeBHist C,
        lagrangianMechanicsEncodeBHist P,
        lagrangianMechanicsEncodeBHist N]

private def lagrangianMechanicsEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lagrangianMechanicsEventAtDefault index rest

def lagrangianMechanicsFromEventFlow (ef : EventFlow) : Option LagrangianMechanicsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LagrangianMechanicsUp.mk
      (lagrangianMechanicsDecodeBHist (lagrangianMechanicsEventAtDefault 0 ef))
      (lagrangianMechanicsDecodeBHist (lagrangianMechanicsEventAtDefault 1 ef))
      (lagrangianMechanicsDecodeBHist (lagrangianMechanicsEventAtDefault 2 ef))
      (lagrangianMechanicsDecodeBHist (lagrangianMechanicsEventAtDefault 3 ef))
      (lagrangianMechanicsDecodeBHist (lagrangianMechanicsEventAtDefault 4 ef))
      (lagrangianMechanicsDecodeBHist (lagrangianMechanicsEventAtDefault 5 ef))
      (lagrangianMechanicsDecodeBHist (lagrangianMechanicsEventAtDefault 6 ef))
      (lagrangianMechanicsDecodeBHist (lagrangianMechanicsEventAtDefault 7 ef))
      (lagrangianMechanicsDecodeBHist (lagrangianMechanicsEventAtDefault 8 ef))
      (lagrangianMechanicsDecodeBHist (lagrangianMechanicsEventAtDefault 9 ef))
      (lagrangianMechanicsDecodeBHist (lagrangianMechanicsEventAtDefault 10 ef))
      (lagrangianMechanicsDecodeBHist (lagrangianMechanicsEventAtDefault 11 ef)))

private theorem LagrangianMechanicsTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LagrangianMechanicsUp,
      lagrangianMechanicsFromEventFlow (lagrangianMechanicsToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q V A R E G S J H C P N =>
      change
        some
          (LagrangianMechanicsUp.mk
            (lagrangianMechanicsDecodeBHist (lagrangianMechanicsEncodeBHist Q))
            (lagrangianMechanicsDecodeBHist (lagrangianMechanicsEncodeBHist V))
            (lagrangianMechanicsDecodeBHist (lagrangianMechanicsEncodeBHist A))
            (lagrangianMechanicsDecodeBHist (lagrangianMechanicsEncodeBHist R))
            (lagrangianMechanicsDecodeBHist (lagrangianMechanicsEncodeBHist E))
            (lagrangianMechanicsDecodeBHist (lagrangianMechanicsEncodeBHist G))
            (lagrangianMechanicsDecodeBHist (lagrangianMechanicsEncodeBHist S))
            (lagrangianMechanicsDecodeBHist (lagrangianMechanicsEncodeBHist J))
            (lagrangianMechanicsDecodeBHist (lagrangianMechanicsEncodeBHist H))
            (lagrangianMechanicsDecodeBHist (lagrangianMechanicsEncodeBHist C))
            (lagrangianMechanicsDecodeBHist (lagrangianMechanicsEncodeBHist P))
            (lagrangianMechanicsDecodeBHist (lagrangianMechanicsEncodeBHist N))) =
          some (LagrangianMechanicsUp.mk Q V A R E G S J H C P N)
      rw [LagrangianMechanicsTasteGate_single_carrier_alignment_decode_encode Q,
        LagrangianMechanicsTasteGate_single_carrier_alignment_decode_encode V,
        LagrangianMechanicsTasteGate_single_carrier_alignment_decode_encode A,
        LagrangianMechanicsTasteGate_single_carrier_alignment_decode_encode R,
        LagrangianMechanicsTasteGate_single_carrier_alignment_decode_encode E,
        LagrangianMechanicsTasteGate_single_carrier_alignment_decode_encode G,
        LagrangianMechanicsTasteGate_single_carrier_alignment_decode_encode S,
        LagrangianMechanicsTasteGate_single_carrier_alignment_decode_encode J,
        LagrangianMechanicsTasteGate_single_carrier_alignment_decode_encode H,
        LagrangianMechanicsTasteGate_single_carrier_alignment_decode_encode C,
        LagrangianMechanicsTasteGate_single_carrier_alignment_decode_encode P,
        LagrangianMechanicsTasteGate_single_carrier_alignment_decode_encode N]

private theorem LagrangianMechanicsTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LagrangianMechanicsUp} :
    lagrangianMechanicsToEventFlow x = lagrangianMechanicsToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lagrangianMechanicsFromEventFlow (lagrangianMechanicsToEventFlow x) =
        lagrangianMechanicsFromEventFlow (lagrangianMechanicsToEventFlow y) :=
    congrArg lagrangianMechanicsFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LagrangianMechanicsTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LagrangianMechanicsTasteGate_single_carrier_alignment_round_trip y)))

instance lagrangianMechanicsBHistCarrier : BHistCarrier LagrangianMechanicsUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lagrangianMechanicsToEventFlow
  fromEventFlow := lagrangianMechanicsFromEventFlow

instance lagrangianMechanicsChapterTasteGate : ChapterTasteGate LagrangianMechanicsUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lagrangianMechanicsFromEventFlow (lagrangianMechanicsToEventFlow x) = some x
    exact LagrangianMechanicsTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LagrangianMechanicsTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate LagrangianMechanicsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  lagrangianMechanicsChapterTasteGate

theorem LagrangianMechanicsTasteGate_single_carrier_alignment :
    (∀ h : BHist, lagrangianMechanicsDecodeBHist (lagrangianMechanicsEncodeBHist h) = h) ∧
      (∀ x : LagrangianMechanicsUp,
        lagrangianMechanicsFromEventFlow (lagrangianMechanicsToEventFlow x) = some x) ∧
        (∀ x y : LagrangianMechanicsUp,
          lagrangianMechanicsToEventFlow x = lagrangianMechanicsToEventFlow y → x = y) ∧
          lagrangianMechanicsEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨LagrangianMechanicsTasteGate_single_carrier_alignment_decode_encode,
      LagrangianMechanicsTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        LagrangianMechanicsTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LagrangianMechanicsUp.TasteGate
