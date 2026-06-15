import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyRoundingProjectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyRoundingProjectionUp : Type where
  | mk (q W D R T S H C P N : BHist) : RegularCauchyRoundingProjectionUp
  deriving DecidableEq

def regularCauchyRoundingProjectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyRoundingProjectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyRoundingProjectionEncodeBHist h

def regularCauchyRoundingProjectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyRoundingProjectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyRoundingProjectionDecodeBHist tail)

private theorem RegularCauchyRoundingProjectionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyRoundingProjectionDecodeBHist
        (regularCauchyRoundingProjectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyRoundingProjectionFields :
    RegularCauchyRoundingProjectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyRoundingProjectionUp.mk q W D R T S H C P N =>
      [q, W, D, R, T, S, H, C, P, N]

def regularCauchyRoundingProjectionToEventFlow :
    RegularCauchyRoundingProjectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchyRoundingProjectionFields x).map
        regularCauchyRoundingProjectionEncodeBHist

private def regularCauchyRoundingProjectionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyRoundingProjectionEventAt index rest

def regularCauchyRoundingProjectionFromEventFlow
    (ef : EventFlow) : Option RegularCauchyRoundingProjectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyRoundingProjectionUp.mk
      (regularCauchyRoundingProjectionDecodeBHist
        (regularCauchyRoundingProjectionEventAt 0 ef))
      (regularCauchyRoundingProjectionDecodeBHist
        (regularCauchyRoundingProjectionEventAt 1 ef))
      (regularCauchyRoundingProjectionDecodeBHist
        (regularCauchyRoundingProjectionEventAt 2 ef))
      (regularCauchyRoundingProjectionDecodeBHist
        (regularCauchyRoundingProjectionEventAt 3 ef))
      (regularCauchyRoundingProjectionDecodeBHist
        (regularCauchyRoundingProjectionEventAt 4 ef))
      (regularCauchyRoundingProjectionDecodeBHist
        (regularCauchyRoundingProjectionEventAt 5 ef))
      (regularCauchyRoundingProjectionDecodeBHist
        (regularCauchyRoundingProjectionEventAt 6 ef))
      (regularCauchyRoundingProjectionDecodeBHist
        (regularCauchyRoundingProjectionEventAt 7 ef))
      (regularCauchyRoundingProjectionDecodeBHist
        (regularCauchyRoundingProjectionEventAt 8 ef))
      (regularCauchyRoundingProjectionDecodeBHist
        (regularCauchyRoundingProjectionEventAt 9 ef)))

private theorem RegularCauchyRoundingProjectionTasteGate_single_carrier_alignment_round_trip
    (x : RegularCauchyRoundingProjectionUp) :
    regularCauchyRoundingProjectionFromEventFlow
      (regularCauchyRoundingProjectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk q W D R T S H C P N =>
      change
        some
          (RegularCauchyRoundingProjectionUp.mk
            (regularCauchyRoundingProjectionDecodeBHist
              (regularCauchyRoundingProjectionEncodeBHist q))
            (regularCauchyRoundingProjectionDecodeBHist
              (regularCauchyRoundingProjectionEncodeBHist W))
            (regularCauchyRoundingProjectionDecodeBHist
              (regularCauchyRoundingProjectionEncodeBHist D))
            (regularCauchyRoundingProjectionDecodeBHist
              (regularCauchyRoundingProjectionEncodeBHist R))
            (regularCauchyRoundingProjectionDecodeBHist
              (regularCauchyRoundingProjectionEncodeBHist T))
            (regularCauchyRoundingProjectionDecodeBHist
              (regularCauchyRoundingProjectionEncodeBHist S))
            (regularCauchyRoundingProjectionDecodeBHist
              (regularCauchyRoundingProjectionEncodeBHist H))
            (regularCauchyRoundingProjectionDecodeBHist
              (regularCauchyRoundingProjectionEncodeBHist C))
            (regularCauchyRoundingProjectionDecodeBHist
              (regularCauchyRoundingProjectionEncodeBHist P))
            (regularCauchyRoundingProjectionDecodeBHist
              (regularCauchyRoundingProjectionEncodeBHist N))) =
          some (RegularCauchyRoundingProjectionUp.mk q W D R T S H C P N)
      rw [RegularCauchyRoundingProjectionTasteGate_single_carrier_alignment_decode_encode q,
        RegularCauchyRoundingProjectionTasteGate_single_carrier_alignment_decode_encode W,
        RegularCauchyRoundingProjectionTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyRoundingProjectionTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchyRoundingProjectionTasteGate_single_carrier_alignment_decode_encode T,
        RegularCauchyRoundingProjectionTasteGate_single_carrier_alignment_decode_encode S,
        RegularCauchyRoundingProjectionTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyRoundingProjectionTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyRoundingProjectionTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyRoundingProjectionTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyRoundingProjectionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyRoundingProjectionUp} :
    regularCauchyRoundingProjectionToEventFlow x =
      regularCauchyRoundingProjectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyRoundingProjectionFromEventFlow
          (regularCauchyRoundingProjectionToEventFlow x) =
        regularCauchyRoundingProjectionFromEventFlow
          (regularCauchyRoundingProjectionToEventFlow y) :=
    congrArg regularCauchyRoundingProjectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyRoundingProjectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyRoundingProjectionTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyRoundingProjectionBHistCarrier :
    BHistCarrier RegularCauchyRoundingProjectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyRoundingProjectionToEventFlow
  fromEventFlow := regularCauchyRoundingProjectionFromEventFlow

instance regularCauchyRoundingProjectionChapterTasteGate :
    ChapterTasteGate RegularCauchyRoundingProjectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyRoundingProjectionFromEventFlow
      (regularCauchyRoundingProjectionToEventFlow x) = some x
    exact RegularCauchyRoundingProjectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyRoundingProjectionTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem RegularCauchyRoundingProjectionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyRoundingProjectionDecodeBHist
        (regularCauchyRoundingProjectionEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyRoundingProjectionUp,
        regularCauchyRoundingProjectionFromEventFlow
          (regularCauchyRoundingProjectionToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyRoundingProjectionUp,
          regularCauchyRoundingProjectionToEventFlow x =
            regularCauchyRoundingProjectionToEventFlow y → x = y) ∧
          regularCauchyRoundingProjectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularCauchyRoundingProjectionTasteGate_single_carrier_alignment_decode_encode,
      RegularCauchyRoundingProjectionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularCauchyRoundingProjectionTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.RegularCauchyRoundingProjectionUp
