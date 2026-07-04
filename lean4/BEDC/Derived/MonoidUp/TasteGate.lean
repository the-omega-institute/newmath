import BEDC.Derived.MonoidUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MonoidUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MonoidUp : Type where
  | mk (carrier : BHist) : MonoidUp
  deriving DecidableEq

def MonoidTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: MonoidTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: MonoidTasteGate_single_carrier_alignment_encodeBHist h

def monoidEncodeBHist : BHist → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  MonoidTasteGate_single_carrier_alignment_encodeBHist

def MonoidTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (MonoidTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (MonoidTasteGate_single_carrier_alignment_decodeBHist tail)

def monoidDecodeBHist : RawEvent → BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  MonoidTasteGate_single_carrier_alignment_decodeBHist

private theorem MonoidTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, monoidDecodeBHist (monoidEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def MonoidTasteGate_single_carrier_alignment_fields : MonoidUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | MonoidUp.mk carrier => [carrier]

def monoidToEventFlow : MonoidUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (MonoidTasteGate_single_carrier_alignment_fields x).map monoidEncodeBHist

private def monoidEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => monoidEventAtDefault index rest

private def monoidEventFlowLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => true
  | Nat.zero, _event :: _rest => false
  | Nat.succ _index, [] => false
  | Nat.succ index, _event :: rest => monoidEventFlowLengthEq index rest

def monoidFromEventFlow (ef : EventFlow) : Option MonoidUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match monoidEventFlowLengthEq 1 ef with
  | true => some (MonoidUp.mk (monoidDecodeBHist (monoidEventAtDefault 0 ef)))
  | false => none

private theorem MonoidTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MonoidUp, monoidFromEventFlow (monoidToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk carrier =>
      change
        some (MonoidUp.mk (monoidDecodeBHist (monoidEncodeBHist carrier))) =
          some (MonoidUp.mk carrier)
      rw [MonoidTasteGate_single_carrier_alignment_decode_encode carrier]

private theorem MonoidTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MonoidUp} :
    monoidToEventFlow x = monoidToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have optionEq : some x = some y := by
    calc
      some x = monoidFromEventFlow (monoidToEventFlow x) :=
        (MonoidTasteGate_single_carrier_alignment_round_trip x).symm
      _ = monoidFromEventFlow (monoidToEventFlow y) :=
        congrArg monoidFromEventFlow heq
      _ = some y := MonoidTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

instance monoidBHistCarrier : BHistCarrier MonoidUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := monoidToEventFlow
  fromEventFlow := monoidFromEventFlow

instance monoidChapterTasteGate : ChapterTasteGate MonoidUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change monoidFromEventFlow (monoidToEventFlow x) = some x
    exact MonoidTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MonoidTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def MonoidTasteGate_single_carrier_alignment_taste_gate : ChapterTasteGate MonoidUp :=
  -- BEDC touchpoint anchor: BHist BMark
  monoidChapterTasteGate

theorem MonoidTasteGate_single_carrier_alignment :
    (forall h : BHist, monoidDecodeBHist (monoidEncodeBHist h) = h) ∧
      (forall x : MonoidUp, monoidFromEventFlow (monoidToEventFlow x) = some x) ∧
      (forall x y : MonoidUp, monoidToEventFlow x = monoidToEventFlow y -> x = y) ∧
      (forall {h k r : BHist}, UnaryHistory h -> UnaryHistory k -> Cont h k r ->
        UnaryHistory r) ∧ monoidEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark Cont UnaryHistory ChapterTasteGate
  constructor
  · exact MonoidTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact MonoidTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact MonoidTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · constructor
        · intro h k r unaryH unaryK route
          exact unary_cont_closed unaryH unaryK route
        · rfl

end BEDC.Derived.MonoidUp
