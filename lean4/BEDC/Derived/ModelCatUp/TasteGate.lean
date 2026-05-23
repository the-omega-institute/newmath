import BEDC.Derived.ModelCatUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ModelCatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ModelCatUp : Type where
  | mk
      (category cof fib weak lift factor provenance rho lambda : BHist) :
      ModelCatUp
  deriving DecidableEq

def modelCatEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: modelCatEncodeBHist h
  | BHist.e1 h => BMark.b1 :: modelCatEncodeBHist h

def modelCatDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (modelCatDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (modelCatDecodeBHist tail)

private theorem modelCat_decode_encode_bhist :
    ∀ h : BHist, modelCatDecodeBHist (modelCatEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def modelCatFields : ModelCatUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ModelCatUp.mk category cof fib weak lift factor provenance rho lambda =>
      [category, cof, fib, weak, lift, factor, provenance, rho, lambda]

def modelCatToEventFlow : ModelCatUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (modelCatFields x).map modelCatEncodeBHist

private def modelCatEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => modelCatEventAtDefault index rest

def modelCatFromEventFlow : EventFlow -> Option ModelCatUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (ModelCatUp.mk
        (modelCatDecodeBHist (modelCatEventAtDefault 0 ef))
        (modelCatDecodeBHist (modelCatEventAtDefault 1 ef))
        (modelCatDecodeBHist (modelCatEventAtDefault 2 ef))
        (modelCatDecodeBHist (modelCatEventAtDefault 3 ef))
        (modelCatDecodeBHist (modelCatEventAtDefault 4 ef))
        (modelCatDecodeBHist (modelCatEventAtDefault 5 ef))
        (modelCatDecodeBHist (modelCatEventAtDefault 6 ef))
        (modelCatDecodeBHist (modelCatEventAtDefault 7 ef))
        (modelCatDecodeBHist (modelCatEventAtDefault 8 ef)))

private theorem modelCat_round_trip :
    ∀ x : ModelCatUp,
      modelCatFromEventFlow (modelCatToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk category cof fib weak lift factor provenance rho lambda =>
      change
        some
          (ModelCatUp.mk
            (modelCatDecodeBHist (modelCatEncodeBHist category))
            (modelCatDecodeBHist (modelCatEncodeBHist cof))
            (modelCatDecodeBHist (modelCatEncodeBHist fib))
            (modelCatDecodeBHist (modelCatEncodeBHist weak))
            (modelCatDecodeBHist (modelCatEncodeBHist lift))
            (modelCatDecodeBHist (modelCatEncodeBHist factor))
            (modelCatDecodeBHist (modelCatEncodeBHist provenance))
            (modelCatDecodeBHist (modelCatEncodeBHist rho))
            (modelCatDecodeBHist (modelCatEncodeBHist lambda))) =
          some
            (ModelCatUp.mk category cof fib weak lift factor provenance rho lambda)
      rw [modelCat_decode_encode_bhist category, modelCat_decode_encode_bhist cof,
        modelCat_decode_encode_bhist fib, modelCat_decode_encode_bhist weak,
        modelCat_decode_encode_bhist lift, modelCat_decode_encode_bhist factor,
        modelCat_decode_encode_bhist provenance, modelCat_decode_encode_bhist rho,
        modelCat_decode_encode_bhist lambda]

private theorem modelCatToEventFlow_injective {x y : ModelCatUp} :
    modelCatToEventFlow x = modelCatToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      modelCatFromEventFlow (modelCatToEventFlow x) =
        modelCatFromEventFlow (modelCatToEventFlow y) :=
    congrArg modelCatFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (modelCat_round_trip x).symm
      (Eq.trans hread (modelCat_round_trip y)))

private theorem modelCat_field_faithful :
    ∀ x y : ModelCatUp, modelCatFields x = modelCatFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk category₁ cof₁ fib₁ weak₁ lift₁ factor₁ provenance₁ rho₁ lambda₁ =>
      cases y with
      | mk category₂ cof₂ fib₂ weak₂ lift₂ factor₂ provenance₂ rho₂ lambda₂ =>
          cases hfields
          rfl

instance modelCatBHistCarrier : BHistCarrier ModelCatUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := modelCatToEventFlow
  fromEventFlow := modelCatFromEventFlow

instance modelCatChapterTasteGate : ChapterTasteGate ModelCatUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change modelCatFromEventFlow (modelCatToEventFlow x) = some x
    exact modelCat_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (modelCatToEventFlow_injective heq)

instance modelCatFieldFaithful : FieldFaithful ModelCatUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := modelCatFields
  field_faithful := modelCat_field_faithful

def taste_gate : ChapterTasteGate ModelCatUp :=
  -- BEDC touchpoint anchor: BHist BMark
  modelCatChapterTasteGate

theorem ModelCatTasteGate_single_carrier_alignment :
    (∀ h : BHist, modelCatDecodeBHist (modelCatEncodeBHist h) = h) ∧
      (∀ x : ModelCatUp,
        modelCatFromEventFlow (modelCatToEventFlow x) = some x) ∧
        (∀ x y : ModelCatUp,
          modelCatToEventFlow x = modelCatToEventFlow y -> x = y) ∧
          modelCatEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨modelCat_decode_encode_bhist,
      modelCat_round_trip,
      (fun _ _ heq => modelCatToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ModelCatUp
