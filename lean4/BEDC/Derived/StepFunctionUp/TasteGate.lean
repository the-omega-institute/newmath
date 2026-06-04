import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StepFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StepFunctionUp : Type where
  | mk (P V A D S I R H C Q N : BHist) : StepFunctionUp
  deriving DecidableEq

def stepFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: stepFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: stepFunctionEncodeBHist h

def stepFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (stepFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (stepFunctionDecodeBHist tail)

private theorem stepFunction_decode_encode :
    ∀ h : BHist, stepFunctionDecodeBHist (stepFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def stepFunctionFields : StepFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StepFunctionUp.mk P V A D S I R H C Q N => [P, V, A, D, S, I, R, H, C, Q, N]

def stepFunctionToEventFlow : StepFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      ([BMark.b1, BMark.b1, BMark.b0] : RawEvent) ::
        (stepFunctionFields x).map stepFunctionEncodeBHist

private def stepFunctionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => stepFunctionEventAtDefault index rest

def stepFunctionFromEventFlow (ef : EventFlow) : Option StepFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (StepFunctionUp.mk
      (stepFunctionDecodeBHist (stepFunctionEventAtDefault 1 ef))
      (stepFunctionDecodeBHist (stepFunctionEventAtDefault 2 ef))
      (stepFunctionDecodeBHist (stepFunctionEventAtDefault 3 ef))
      (stepFunctionDecodeBHist (stepFunctionEventAtDefault 4 ef))
      (stepFunctionDecodeBHist (stepFunctionEventAtDefault 5 ef))
      (stepFunctionDecodeBHist (stepFunctionEventAtDefault 6 ef))
      (stepFunctionDecodeBHist (stepFunctionEventAtDefault 7 ef))
      (stepFunctionDecodeBHist (stepFunctionEventAtDefault 8 ef))
      (stepFunctionDecodeBHist (stepFunctionEventAtDefault 9 ef))
      (stepFunctionDecodeBHist (stepFunctionEventAtDefault 10 ef))
      (stepFunctionDecodeBHist (stepFunctionEventAtDefault 11 ef)))

private theorem stepFunction_round_trip :
    ∀ x : StepFunctionUp,
      stepFunctionFromEventFlow (stepFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk P V A D S I R H C Q N =>
      change
        some
          (StepFunctionUp.mk
            (stepFunctionDecodeBHist (stepFunctionEncodeBHist P))
            (stepFunctionDecodeBHist (stepFunctionEncodeBHist V))
            (stepFunctionDecodeBHist (stepFunctionEncodeBHist A))
            (stepFunctionDecodeBHist (stepFunctionEncodeBHist D))
            (stepFunctionDecodeBHist (stepFunctionEncodeBHist S))
            (stepFunctionDecodeBHist (stepFunctionEncodeBHist I))
            (stepFunctionDecodeBHist (stepFunctionEncodeBHist R))
            (stepFunctionDecodeBHist (stepFunctionEncodeBHist H))
            (stepFunctionDecodeBHist (stepFunctionEncodeBHist C))
            (stepFunctionDecodeBHist (stepFunctionEncodeBHist Q))
            (stepFunctionDecodeBHist (stepFunctionEncodeBHist N))) =
          some (StepFunctionUp.mk P V A D S I R H C Q N)
      rw [stepFunction_decode_encode P, stepFunction_decode_encode V,
        stepFunction_decode_encode A, stepFunction_decode_encode D,
        stepFunction_decode_encode S, stepFunction_decode_encode I,
        stepFunction_decode_encode R, stepFunction_decode_encode H,
        stepFunction_decode_encode C, stepFunction_decode_encode Q,
        stepFunction_decode_encode N]

private theorem stepFunctionToEventFlow_injective {x y : StepFunctionUp} :
    stepFunctionToEventFlow x = stepFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = stepFunctionFromEventFlow (stepFunctionToEventFlow x) :=
        (stepFunction_round_trip x).symm
      _ = stepFunctionFromEventFlow (stepFunctionToEventFlow y) :=
        congrArg stepFunctionFromEventFlow hxy
      _ = some y := stepFunction_round_trip y
  exact Option.some.inj optionEq

private theorem stepFunction_field_faithful :
    ∀ x y : StepFunctionUp, stepFunctionFields x = stepFunctionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk P V A D S I R H C Q N =>
      cases y with
      | mk P' V' A' D' S' I' R' H' C' Q' N' =>
          cases hfields
          rfl

instance stepFunctionBHistCarrier : BHistCarrier StepFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := stepFunctionToEventFlow
  fromEventFlow := stepFunctionFromEventFlow

instance stepFunctionChapterTasteGate : ChapterTasteGate StepFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change stepFunctionFromEventFlow (stepFunctionToEventFlow x) = some x
    exact stepFunction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (stepFunctionToEventFlow_injective heq)

instance stepFunctionFieldFaithful : FieldFaithful StepFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := stepFunctionFields
  field_faithful := stepFunction_field_faithful

instance stepFunctionNontrivial : Nontrivial StepFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨StepFunctionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      StepFunctionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate StepFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  stepFunctionChapterTasteGate

theorem StepFunctionTasteGate_single_carrier_alignment :
    ChapterTasteGate StepFunctionUp ∧ Nonempty (Nontrivial StepFunctionUp) ∧
      Nonempty (FieldFaithful StepFunctionUp) ∧
        (∀ h : BHist, stepFunctionDecodeBHist (stepFunctionEncodeBHist h) = h) ∧
          (∀ x : StepFunctionUp,
            stepFunctionFromEventFlow (stepFunctionToEventFlow x) = some x) ∧
            stepFunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨stepFunctionChapterTasteGate, ⟨stepFunctionNontrivial⟩,
      ⟨stepFunctionFieldFaithful⟩, stepFunction_decode_encode, stepFunction_round_trip, rfl⟩

end BEDC.Derived.StepFunctionUp
