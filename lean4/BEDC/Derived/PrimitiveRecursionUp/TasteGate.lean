import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PrimitiveRecursionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PrimitiveRecursionUp : Type where
  | mk (D S T U W Q H C P N : BHist) : PrimitiveRecursionUp
  deriving DecidableEq

def primitiveRecursionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: primitiveRecursionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: primitiveRecursionEncodeBHist h

def primitiveRecursionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (primitiveRecursionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (primitiveRecursionDecodeBHist tail)

private theorem primitiveRecursion_decode_encode :
    ∀ h : BHist, primitiveRecursionDecodeBHist (primitiveRecursionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def primitiveRecursionToEventFlow : PrimitiveRecursionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PrimitiveRecursionUp.mk D S T U W Q H C P N =>
      [primitiveRecursionEncodeBHist D, primitiveRecursionEncodeBHist S,
        primitiveRecursionEncodeBHist T, primitiveRecursionEncodeBHist U,
        primitiveRecursionEncodeBHist W, primitiveRecursionEncodeBHist Q,
        primitiveRecursionEncodeBHist H, primitiveRecursionEncodeBHist C,
        primitiveRecursionEncodeBHist P, primitiveRecursionEncodeBHist N]

def primitiveRecursionFromEventFlow (flow : EventFlow) : Option PrimitiveRecursionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match flow with
  | [] => none
  | D :: rest =>
      match rest with
      | [] => none
      | S :: rest =>
          match rest with
          | [] => none
          | T :: rest =>
              match rest with
              | [] => none
              | U :: rest =>
                  match rest with
                  | [] => none
                  | W :: rest =>
                      match rest with
                      | [] => none
                      | Q :: rest =>
                          match rest with
                          | [] => none
                          | H :: rest =>
                              match rest with
                              | [] => none
                              | C :: rest =>
                                  match rest with
                                  | [] => none
                                  | P :: rest =>
                                      match rest with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (PrimitiveRecursionUp.mk
                                                  (primitiveRecursionDecodeBHist D)
                                                  (primitiveRecursionDecodeBHist S)
                                                  (primitiveRecursionDecodeBHist T)
                                                  (primitiveRecursionDecodeBHist U)
                                                  (primitiveRecursionDecodeBHist W)
                                                  (primitiveRecursionDecodeBHist Q)
                                                  (primitiveRecursionDecodeBHist H)
                                                  (primitiveRecursionDecodeBHist C)
                                                  (primitiveRecursionDecodeBHist P)
                                                  (primitiveRecursionDecodeBHist N))
                                          | _ :: _ => none

private theorem primitiveRecursion_round_trip :
    ∀ x : PrimitiveRecursionUp,
      primitiveRecursionFromEventFlow (primitiveRecursionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S T U W Q H C P N =>
      rw [primitiveRecursionToEventFlow, primitiveRecursionFromEventFlow,
        primitiveRecursion_decode_encode D, primitiveRecursion_decode_encode S,
        primitiveRecursion_decode_encode T, primitiveRecursion_decode_encode U,
        primitiveRecursion_decode_encode W, primitiveRecursion_decode_encode Q,
        primitiveRecursion_decode_encode H, primitiveRecursion_decode_encode C,
        primitiveRecursion_decode_encode P, primitiveRecursion_decode_encode N]

private theorem primitiveRecursionToEventFlow_injective {x y : PrimitiveRecursionUp} :
    primitiveRecursionToEventFlow x = primitiveRecursionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      primitiveRecursionFromEventFlow (primitiveRecursionToEventFlow x) =
        primitiveRecursionFromEventFlow (primitiveRecursionToEventFlow y) :=
    congrArg primitiveRecursionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (primitiveRecursion_round_trip x).symm
      (Eq.trans hread (primitiveRecursion_round_trip y)))

instance primitiveRecursionBHistCarrier : BHistCarrier PrimitiveRecursionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := primitiveRecursionToEventFlow
  fromEventFlow := primitiveRecursionFromEventFlow

instance primitiveRecursionChapterTasteGate : ChapterTasteGate PrimitiveRecursionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change primitiveRecursionFromEventFlow (primitiveRecursionToEventFlow x) = some x
    exact primitiveRecursion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (primitiveRecursionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate PrimitiveRecursionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  primitiveRecursionChapterTasteGate

theorem PrimitiveRecursionUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, primitiveRecursionDecodeBHist (primitiveRecursionEncodeBHist h) = h) ∧
      (∀ x : PrimitiveRecursionUp,
        primitiveRecursionFromEventFlow (primitiveRecursionToEventFlow x) = some x) ∧
      (∀ x y : PrimitiveRecursionUp,
        primitiveRecursionToEventFlow x = primitiveRecursionToEventFlow y → x = y) ∧
      primitiveRecursionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨primitiveRecursion_decode_encode,
      primitiveRecursion_round_trip,
      fun _ _ heq => primitiveRecursionToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.PrimitiveRecursionUp
