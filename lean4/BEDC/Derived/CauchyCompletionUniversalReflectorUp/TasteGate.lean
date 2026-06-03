import BEDC.Derived.CauchyCompletionUniversalReflectorUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionUniversalReflectorUp

open BEDC.Derived
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def cauchyCompletionUniversalReflectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionUniversalReflectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionUniversalReflectorEncodeBHist h

def cauchyCompletionUniversalReflectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionUniversalReflectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionUniversalReflectorDecodeBHist tail)

private theorem CauchyCompletionUniversalReflectorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyCompletionUniversalReflectorDecodeBHist
        (cauchyCompletionUniversalReflectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionUniversalReflectorToEventFlow :
    CauchyCompletionUniversalReflectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionUniversalReflectorUp.carrier =>
      [cauchyCompletionUniversalReflectorEncodeBHist BHist.Empty]

private def cauchyCompletionUniversalReflectorRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => cauchyCompletionUniversalReflectorRawAt n rest

private def cauchyCompletionUniversalReflectorLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => cauchyCompletionUniversalReflectorLengthEq n rest

def cauchyCompletionUniversalReflectorFromEventFlow :
    EventFlow → Option CauchyCompletionUniversalReflectorUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match cauchyCompletionUniversalReflectorLengthEq 1 flow with
      | true =>
          match cauchyCompletionUniversalReflectorDecodeBHist
              (cauchyCompletionUniversalReflectorRawAt 0 flow) with
          | BHist.Empty => some CauchyCompletionUniversalReflectorUp.carrier
          | BHist.e0 _ => none
          | BHist.e1 _ => none
      | false => none

private theorem cauchyCompletionUniversalReflector_round_trip :
    ∀ x : CauchyCompletionUniversalReflectorUp,
      cauchyCompletionUniversalReflectorFromEventFlow
        (cauchyCompletionUniversalReflectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x
  rfl

private theorem cauchyCompletionUniversalReflectorToEventFlow_injective
    {x y : CauchyCompletionUniversalReflectorUp} :
    cauchyCompletionUniversalReflectorToEventFlow x =
      cauchyCompletionUniversalReflectorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro _heq
  cases x
  cases y
  rfl

instance cauchyCompletionUniversalReflectorBHistCarrier :
    BHistCarrier CauchyCompletionUniversalReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionUniversalReflectorToEventFlow
  fromEventFlow := cauchyCompletionUniversalReflectorFromEventFlow

instance cauchyCompletionUniversalReflectorChapterTasteGate :
    ChapterTasteGate CauchyCompletionUniversalReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionUniversalReflectorFromEventFlow
        (cauchyCompletionUniversalReflectorToEventFlow x) = some x
    exact cauchyCompletionUniversalReflector_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletionUniversalReflectorToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyCompletionUniversalReflectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionUniversalReflectorChapterTasteGate

theorem CauchyCompletionUniversalReflectorTasteGate_single_carrier_alignment :
    (forall h : BHist,
      cauchyCompletionUniversalReflectorDecodeBHist
        (cauchyCompletionUniversalReflectorEncodeBHist h) = h) ∧
      (forall x : CauchyCompletionUniversalReflectorUp,
        cauchyCompletionUniversalReflectorFromEventFlow
          (cauchyCompletionUniversalReflectorToEventFlow x) = some x) ∧
        (forall x y : CauchyCompletionUniversalReflectorUp,
          cauchyCompletionUniversalReflectorToEventFlow x =
            cauchyCompletionUniversalReflectorToEventFlow y -> x = y) ∧
          cauchyCompletionUniversalReflectorEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyCompletionUniversalReflectorTasteGate_single_carrier_alignment_decode,
      cauchyCompletionUniversalReflector_round_trip,
      fun _ _ heq => cauchyCompletionUniversalReflectorToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.CauchyCompletionUniversalReflectorUp
