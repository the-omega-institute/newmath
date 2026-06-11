import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedCauchyFilterCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedCauchyFilterCompletionUp : Type where
  | mk (C F U W T R L H K P N : BHist) : BoundedCauchyFilterCompletionUp
  deriving DecidableEq

def boundedCauchyFilterCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedCauchyFilterCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedCauchyFilterCompletionEncodeBHist h

def boundedCauchyFilterCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedCauchyFilterCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedCauchyFilterCompletionDecodeBHist tail)

private theorem BoundedCauchyFilterCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      boundedCauchyFilterCompletionDecodeBHist
        (boundedCauchyFilterCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def boundedCauchyFilterCompletionFields : BoundedCauchyFilterCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedCauchyFilterCompletionUp.mk C F U W T R L H K P N =>
      [C, F, U, W, T, R, L, H, K, P, N]

def boundedCauchyFilterCompletionToEventFlow : BoundedCauchyFilterCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (boundedCauchyFilterCompletionFields x).map
      boundedCauchyFilterCompletionEncodeBHist

private def boundedCauchyFilterCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      boundedCauchyFilterCompletionEventAtDefault index rest

def boundedCauchyFilterCompletionFromEventFlow
    (ef : EventFlow) : Option BoundedCauchyFilterCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BoundedCauchyFilterCompletionUp.mk
      (boundedCauchyFilterCompletionDecodeBHist
        (boundedCauchyFilterCompletionEventAtDefault 0 ef))
      (boundedCauchyFilterCompletionDecodeBHist
        (boundedCauchyFilterCompletionEventAtDefault 1 ef))
      (boundedCauchyFilterCompletionDecodeBHist
        (boundedCauchyFilterCompletionEventAtDefault 2 ef))
      (boundedCauchyFilterCompletionDecodeBHist
        (boundedCauchyFilterCompletionEventAtDefault 3 ef))
      (boundedCauchyFilterCompletionDecodeBHist
        (boundedCauchyFilterCompletionEventAtDefault 4 ef))
      (boundedCauchyFilterCompletionDecodeBHist
        (boundedCauchyFilterCompletionEventAtDefault 5 ef))
      (boundedCauchyFilterCompletionDecodeBHist
        (boundedCauchyFilterCompletionEventAtDefault 6 ef))
      (boundedCauchyFilterCompletionDecodeBHist
        (boundedCauchyFilterCompletionEventAtDefault 7 ef))
      (boundedCauchyFilterCompletionDecodeBHist
        (boundedCauchyFilterCompletionEventAtDefault 8 ef))
      (boundedCauchyFilterCompletionDecodeBHist
        (boundedCauchyFilterCompletionEventAtDefault 9 ef))
      (boundedCauchyFilterCompletionDecodeBHist
        (boundedCauchyFilterCompletionEventAtDefault 10 ef)))

private theorem BoundedCauchyFilterCompletionTasteGate_single_carrier_alignment_round_trip
    (x : BoundedCauchyFilterCompletionUp) :
    boundedCauchyFilterCompletionFromEventFlow
        (boundedCauchyFilterCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk C F U W T R L H K P N =>
      change
        some
          (BoundedCauchyFilterCompletionUp.mk
            (boundedCauchyFilterCompletionDecodeBHist
              (boundedCauchyFilterCompletionEncodeBHist C))
            (boundedCauchyFilterCompletionDecodeBHist
              (boundedCauchyFilterCompletionEncodeBHist F))
            (boundedCauchyFilterCompletionDecodeBHist
              (boundedCauchyFilterCompletionEncodeBHist U))
            (boundedCauchyFilterCompletionDecodeBHist
              (boundedCauchyFilterCompletionEncodeBHist W))
            (boundedCauchyFilterCompletionDecodeBHist
              (boundedCauchyFilterCompletionEncodeBHist T))
            (boundedCauchyFilterCompletionDecodeBHist
              (boundedCauchyFilterCompletionEncodeBHist R))
            (boundedCauchyFilterCompletionDecodeBHist
              (boundedCauchyFilterCompletionEncodeBHist L))
            (boundedCauchyFilterCompletionDecodeBHist
              (boundedCauchyFilterCompletionEncodeBHist H))
            (boundedCauchyFilterCompletionDecodeBHist
              (boundedCauchyFilterCompletionEncodeBHist K))
            (boundedCauchyFilterCompletionDecodeBHist
              (boundedCauchyFilterCompletionEncodeBHist P))
            (boundedCauchyFilterCompletionDecodeBHist
              (boundedCauchyFilterCompletionEncodeBHist N))) =
          some (BoundedCauchyFilterCompletionUp.mk C F U W T R L H K P N)
      rw [BoundedCauchyFilterCompletionTasteGate_single_carrier_alignment_decode_encode C,
        BoundedCauchyFilterCompletionTasteGate_single_carrier_alignment_decode_encode F,
        BoundedCauchyFilterCompletionTasteGate_single_carrier_alignment_decode_encode U,
        BoundedCauchyFilterCompletionTasteGate_single_carrier_alignment_decode_encode W,
        BoundedCauchyFilterCompletionTasteGate_single_carrier_alignment_decode_encode T,
        BoundedCauchyFilterCompletionTasteGate_single_carrier_alignment_decode_encode R,
        BoundedCauchyFilterCompletionTasteGate_single_carrier_alignment_decode_encode L,
        BoundedCauchyFilterCompletionTasteGate_single_carrier_alignment_decode_encode H,
        BoundedCauchyFilterCompletionTasteGate_single_carrier_alignment_decode_encode K,
        BoundedCauchyFilterCompletionTasteGate_single_carrier_alignment_decode_encode P,
        BoundedCauchyFilterCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem BoundedCauchyFilterCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BoundedCauchyFilterCompletionUp} :
    boundedCauchyFilterCompletionToEventFlow x =
      boundedCauchyFilterCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedCauchyFilterCompletionFromEventFlow
          (boundedCauchyFilterCompletionToEventFlow x) =
        boundedCauchyFilterCompletionFromEventFlow
          (boundedCauchyFilterCompletionToEventFlow y) :=
    congrArg boundedCauchyFilterCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BoundedCauchyFilterCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BoundedCauchyFilterCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance boundedCauchyFilterCompletionBHistCarrier :
    BHistCarrier BoundedCauchyFilterCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedCauchyFilterCompletionToEventFlow
  fromEventFlow := boundedCauchyFilterCompletionFromEventFlow

instance boundedCauchyFilterCompletionChapterTasteGate :
    ChapterTasteGate BoundedCauchyFilterCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      boundedCauchyFilterCompletionFromEventFlow
        (boundedCauchyFilterCompletionToEventFlow x) = some x
    exact BoundedCauchyFilterCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BoundedCauchyFilterCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem BoundedCauchyFilterCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      boundedCauchyFilterCompletionDecodeBHist
        (boundedCauchyFilterCompletionEncodeBHist h) = h) ∧
      (∀ x : BoundedCauchyFilterCompletionUp,
        boundedCauchyFilterCompletionFromEventFlow
          (boundedCauchyFilterCompletionToEventFlow x) = some x) ∧
        (∀ x y : BoundedCauchyFilterCompletionUp,
          boundedCauchyFilterCompletionToEventFlow x =
            boundedCauchyFilterCompletionToEventFlow y → x = y) ∧
          boundedCauchyFilterCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BoundedCauchyFilterCompletionTasteGate_single_carrier_alignment_decode_encode,
      BoundedCauchyFilterCompletionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BoundedCauchyFilterCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.BoundedCauchyFilterCompletionUp
