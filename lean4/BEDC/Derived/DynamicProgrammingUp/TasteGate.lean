import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DynamicProgrammingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DynamicProgrammingUp : Type where
  | mk (state action transition cost horizon value policy route localName :
      BHist) : DynamicProgrammingUp
  deriving DecidableEq

def dynamicProgrammingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dynamicProgrammingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dynamicProgrammingEncodeBHist h

def dynamicProgrammingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dynamicProgrammingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dynamicProgrammingDecodeBHist tail)

private theorem dynamicProgrammingDecode_encode_bhist :
    ∀ h : BHist, dynamicProgrammingDecodeBHist (dynamicProgrammingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dynamicProgrammingFields : DynamicProgrammingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DynamicProgrammingUp.mk state action transition cost horizon value policy route
      localName =>
      [state, action, transition, cost, horizon, value, policy, route, localName]

def dynamicProgrammingToEventFlow : DynamicProgrammingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dynamicProgrammingFields x).map dynamicProgrammingEncodeBHist

private def dynamicProgrammingEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dynamicProgrammingEventAtDefault index rest

def dynamicProgrammingFromEventFlow (ef : EventFlow) : Option DynamicProgrammingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DynamicProgrammingUp.mk
      (dynamicProgrammingDecodeBHist (dynamicProgrammingEventAtDefault 0 ef))
      (dynamicProgrammingDecodeBHist (dynamicProgrammingEventAtDefault 1 ef))
      (dynamicProgrammingDecodeBHist (dynamicProgrammingEventAtDefault 2 ef))
      (dynamicProgrammingDecodeBHist (dynamicProgrammingEventAtDefault 3 ef))
      (dynamicProgrammingDecodeBHist (dynamicProgrammingEventAtDefault 4 ef))
      (dynamicProgrammingDecodeBHist (dynamicProgrammingEventAtDefault 5 ef))
      (dynamicProgrammingDecodeBHist (dynamicProgrammingEventAtDefault 6 ef))
      (dynamicProgrammingDecodeBHist (dynamicProgrammingEventAtDefault 7 ef))
      (dynamicProgrammingDecodeBHist (dynamicProgrammingEventAtDefault 8 ef)))

private theorem dynamicProgramming_round_trip :
    ∀ x : DynamicProgrammingUp,
      dynamicProgrammingFromEventFlow (dynamicProgrammingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk state action transition cost horizon value policy route localName =>
      change
        some
          (DynamicProgrammingUp.mk
            (dynamicProgrammingDecodeBHist (dynamicProgrammingEncodeBHist state))
            (dynamicProgrammingDecodeBHist (dynamicProgrammingEncodeBHist action))
            (dynamicProgrammingDecodeBHist (dynamicProgrammingEncodeBHist transition))
            (dynamicProgrammingDecodeBHist (dynamicProgrammingEncodeBHist cost))
            (dynamicProgrammingDecodeBHist (dynamicProgrammingEncodeBHist horizon))
            (dynamicProgrammingDecodeBHist (dynamicProgrammingEncodeBHist value))
            (dynamicProgrammingDecodeBHist (dynamicProgrammingEncodeBHist policy))
            (dynamicProgrammingDecodeBHist (dynamicProgrammingEncodeBHist route))
            (dynamicProgrammingDecodeBHist (dynamicProgrammingEncodeBHist localName))) =
          some
            (DynamicProgrammingUp.mk state action transition cost horizon value policy route
              localName)
      rw [dynamicProgrammingDecode_encode_bhist state,
        dynamicProgrammingDecode_encode_bhist action,
        dynamicProgrammingDecode_encode_bhist transition,
        dynamicProgrammingDecode_encode_bhist cost,
        dynamicProgrammingDecode_encode_bhist horizon,
        dynamicProgrammingDecode_encode_bhist value,
        dynamicProgrammingDecode_encode_bhist policy,
        dynamicProgrammingDecode_encode_bhist route,
        dynamicProgrammingDecode_encode_bhist localName]

private theorem dynamicProgrammingToEventFlow_injective {x y : DynamicProgrammingUp} :
    dynamicProgrammingToEventFlow x = dynamicProgrammingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dynamicProgrammingFromEventFlow (dynamicProgrammingToEventFlow x) =
        dynamicProgrammingFromEventFlow (dynamicProgrammingToEventFlow y) :=
    congrArg dynamicProgrammingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dynamicProgramming_round_trip x).symm
      (Eq.trans hread (dynamicProgramming_round_trip y)))

private theorem dynamicProgramming_fields_faithful :
    ∀ x y : DynamicProgrammingUp, dynamicProgrammingFields x = dynamicProgrammingFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk state1 action1 transition1 cost1 horizon1 value1 policy1 route1 localName1 =>
      cases y with
      | mk state2 action2 transition2 cost2 horizon2 value2 policy2 route2 localName2 =>
          cases hfields
          rfl

instance dynamicProgrammingBHistCarrier : BHistCarrier DynamicProgrammingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dynamicProgrammingToEventFlow
  fromEventFlow := dynamicProgrammingFromEventFlow

instance dynamicProgrammingChapterTasteGate : ChapterTasteGate DynamicProgrammingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dynamicProgrammingFromEventFlow (dynamicProgrammingToEventFlow x) = some x
    exact dynamicProgramming_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dynamicProgrammingToEventFlow_injective heq)

instance dynamicProgrammingFieldFaithful : FieldFaithful DynamicProgrammingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dynamicProgrammingFields
  field_faithful := dynamicProgramming_fields_faithful

instance dynamicProgrammingNontrivial : Nontrivial DynamicProgrammingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DynamicProgrammingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DynamicProgrammingUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DynamicProgrammingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dynamicProgrammingChapterTasteGate

theorem DynamicProgrammingTasteGate_single_carrier_alignment :
    (∀ x : DynamicProgrammingUp,
        dynamicProgrammingFromEventFlow (dynamicProgrammingToEventFlow x) = some x) ∧
      (∀ x y : DynamicProgrammingUp,
        dynamicProgrammingFields x = dynamicProgrammingFields y → x = y) ∧
        dynamicProgrammingEncodeBHist BHist.Empty = ([] : RawEvent) ∧
          dynamicProgrammingEncodeBHist (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨dynamicProgramming_round_trip, dynamicProgramming_fields_faithful, rfl, rfl⟩

end BEDC.Derived.DynamicProgrammingUp
