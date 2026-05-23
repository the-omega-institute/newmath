import BEDC.Derived.DerivativeUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DerivativeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DerivativeUp : Type where
  | mk (function point step quotient distance : BHist) : DerivativeUp
  deriving DecidableEq

def derivativeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: derivativeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: derivativeEncodeBHist h

def derivativeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (derivativeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (derivativeDecodeBHist tail)

private theorem DerivativeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, derivativeDecodeBHist (derivativeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def derivativeFields : DerivativeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DerivativeUp.mk function point step quotient distance =>
      [function, point, step, quotient, distance]

def derivativeToEventFlow : DerivativeUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (derivativeFields x).map derivativeEncodeBHist

def derivativeFromEventFlow : EventFlow → Option DerivativeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | function :: rest0 =>
      match rest0 with
      | [] => none
      | point :: rest1 =>
          match rest1 with
          | [] => none
          | step :: rest2 =>
              match rest2 with
              | [] => none
              | quotient :: rest3 =>
                  match rest3 with
                  | [] => none
                  | distance :: rest4 =>
                      match rest4 with
                      | [] =>
                          some
                            (DerivativeUp.mk
                              (derivativeDecodeBHist function)
                              (derivativeDecodeBHist point)
                              (derivativeDecodeBHist step)
                              (derivativeDecodeBHist quotient)
                              (derivativeDecodeBHist distance))
                      | _ :: _ => none

private theorem DerivativeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DerivativeUp, derivativeFromEventFlow (derivativeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk function point step quotient distance =>
      change
        some
            (DerivativeUp.mk
              (derivativeDecodeBHist (derivativeEncodeBHist function))
              (derivativeDecodeBHist (derivativeEncodeBHist point))
              (derivativeDecodeBHist (derivativeEncodeBHist step))
              (derivativeDecodeBHist (derivativeEncodeBHist quotient))
              (derivativeDecodeBHist (derivativeEncodeBHist distance))) =
          some (DerivativeUp.mk function point step quotient distance)
      rw [DerivativeTasteGate_single_carrier_alignment_decode_encode function,
        DerivativeTasteGate_single_carrier_alignment_decode_encode point,
        DerivativeTasteGate_single_carrier_alignment_decode_encode step,
        DerivativeTasteGate_single_carrier_alignment_decode_encode quotient,
        DerivativeTasteGate_single_carrier_alignment_decode_encode distance]

private theorem DerivativeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DerivativeUp} :
    derivativeToEventFlow x = derivativeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      derivativeFromEventFlow (derivativeToEventFlow x) =
        derivativeFromEventFlow (derivativeToEventFlow y) :=
    congrArg derivativeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DerivativeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DerivativeTasteGate_single_carrier_alignment_round_trip y)))

instance derivativeBHistCarrier : BHistCarrier DerivativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := derivativeToEventFlow
  fromEventFlow := derivativeFromEventFlow

instance derivativeChapterTasteGate : ChapterTasteGate DerivativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change derivativeFromEventFlow (derivativeToEventFlow x) = some x
    exact DerivativeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DerivativeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem DerivativeTasteGate_single_carrier_alignment :
    (∀ h : BHist, derivativeDecodeBHist (derivativeEncodeBHist h) = h) ∧
      (∀ x : DerivativeUp, derivativeFromEventFlow (derivativeToEventFlow x) = some x) ∧
        (∀ x y : DerivativeUp, derivativeToEventFlow x = derivativeToEventFlow y → x = y) ∧
          derivativeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨DerivativeTasteGate_single_carrier_alignment_decode_encode,
      DerivativeTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => DerivativeTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DerivativeUp
