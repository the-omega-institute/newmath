import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArzelaAscoliFiniteWindowDiagonalBridgeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ArzelaAscoliFiniteWindowDiagonalBridgeUp : Type where
  | mk (K E Y D W R S H C P N : BHist) : ArzelaAscoliFiniteWindowDiagonalBridgeUp
  deriving DecidableEq

def arzelaAscoliFiniteWindowDiagonalBridgeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: arzelaAscoliFiniteWindowDiagonalBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: arzelaAscoliFiniteWindowDiagonalBridgeEncodeBHist h

def arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist tail)

private theorem ArzelaAscoliFiniteWindowDiagonalBridgeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist
        (arzelaAscoliFiniteWindowDiagonalBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def arzelaAscoliFiniteWindowDiagonalBridgeFields :
    ArzelaAscoliFiniteWindowDiagonalBridgeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ArzelaAscoliFiniteWindowDiagonalBridgeUp.mk K E Y D W R S H C P N =>
      [K, E, Y, D, W, R, S, H, C, P, N]

def arzelaAscoliFiniteWindowDiagonalBridgeToEventFlow :
    ArzelaAscoliFiniteWindowDiagonalBridgeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (arzelaAscoliFiniteWindowDiagonalBridgeFields x).map
        arzelaAscoliFiniteWindowDiagonalBridgeEncodeBHist

private def arzelaAscoliFiniteWindowDiagonalBridgeEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => arzelaAscoliFiniteWindowDiagonalBridgeEventAt index rest

def arzelaAscoliFiniteWindowDiagonalBridgeFromEventFlow
    (flow : EventFlow) : Option ArzelaAscoliFiniteWindowDiagonalBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ArzelaAscoliFiniteWindowDiagonalBridgeUp.mk
      (arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist
        (arzelaAscoliFiniteWindowDiagonalBridgeEventAt 0 flow))
      (arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist
        (arzelaAscoliFiniteWindowDiagonalBridgeEventAt 1 flow))
      (arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist
        (arzelaAscoliFiniteWindowDiagonalBridgeEventAt 2 flow))
      (arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist
        (arzelaAscoliFiniteWindowDiagonalBridgeEventAt 3 flow))
      (arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist
        (arzelaAscoliFiniteWindowDiagonalBridgeEventAt 4 flow))
      (arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist
        (arzelaAscoliFiniteWindowDiagonalBridgeEventAt 5 flow))
      (arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist
        (arzelaAscoliFiniteWindowDiagonalBridgeEventAt 6 flow))
      (arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist
        (arzelaAscoliFiniteWindowDiagonalBridgeEventAt 7 flow))
      (arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist
        (arzelaAscoliFiniteWindowDiagonalBridgeEventAt 8 flow))
      (arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist
        (arzelaAscoliFiniteWindowDiagonalBridgeEventAt 9 flow))
      (arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist
        (arzelaAscoliFiniteWindowDiagonalBridgeEventAt 10 flow)))

private theorem ArzelaAscoliFiniteWindowDiagonalBridgeTasteGate_single_carrier_alignment_round_trip
    (x : ArzelaAscoliFiniteWindowDiagonalBridgeUp) :
    arzelaAscoliFiniteWindowDiagonalBridgeFromEventFlow
      (arzelaAscoliFiniteWindowDiagonalBridgeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K E Y D W R S H C P N =>
      change
        some
          (ArzelaAscoliFiniteWindowDiagonalBridgeUp.mk
            (arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist
              (arzelaAscoliFiniteWindowDiagonalBridgeEncodeBHist K))
            (arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist
              (arzelaAscoliFiniteWindowDiagonalBridgeEncodeBHist E))
            (arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist
              (arzelaAscoliFiniteWindowDiagonalBridgeEncodeBHist Y))
            (arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist
              (arzelaAscoliFiniteWindowDiagonalBridgeEncodeBHist D))
            (arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist
              (arzelaAscoliFiniteWindowDiagonalBridgeEncodeBHist W))
            (arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist
              (arzelaAscoliFiniteWindowDiagonalBridgeEncodeBHist R))
            (arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist
              (arzelaAscoliFiniteWindowDiagonalBridgeEncodeBHist S))
            (arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist
              (arzelaAscoliFiniteWindowDiagonalBridgeEncodeBHist H))
            (arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist
              (arzelaAscoliFiniteWindowDiagonalBridgeEncodeBHist C))
            (arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist
              (arzelaAscoliFiniteWindowDiagonalBridgeEncodeBHist P))
            (arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist
              (arzelaAscoliFiniteWindowDiagonalBridgeEncodeBHist N))) =
          some (ArzelaAscoliFiniteWindowDiagonalBridgeUp.mk K E Y D W R S H C P N)
      rw [
        ArzelaAscoliFiniteWindowDiagonalBridgeTasteGate_single_carrier_alignment_decode_encode K,
        ArzelaAscoliFiniteWindowDiagonalBridgeTasteGate_single_carrier_alignment_decode_encode E,
        ArzelaAscoliFiniteWindowDiagonalBridgeTasteGate_single_carrier_alignment_decode_encode Y,
        ArzelaAscoliFiniteWindowDiagonalBridgeTasteGate_single_carrier_alignment_decode_encode D,
        ArzelaAscoliFiniteWindowDiagonalBridgeTasteGate_single_carrier_alignment_decode_encode W,
        ArzelaAscoliFiniteWindowDiagonalBridgeTasteGate_single_carrier_alignment_decode_encode R,
        ArzelaAscoliFiniteWindowDiagonalBridgeTasteGate_single_carrier_alignment_decode_encode S,
        ArzelaAscoliFiniteWindowDiagonalBridgeTasteGate_single_carrier_alignment_decode_encode H,
        ArzelaAscoliFiniteWindowDiagonalBridgeTasteGate_single_carrier_alignment_decode_encode C,
        ArzelaAscoliFiniteWindowDiagonalBridgeTasteGate_single_carrier_alignment_decode_encode P,
        ArzelaAscoliFiniteWindowDiagonalBridgeTasteGate_single_carrier_alignment_decode_encode N]

private theorem ArzelaAscoliFiniteWindowDiagonalBridgeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ArzelaAscoliFiniteWindowDiagonalBridgeUp} :
    arzelaAscoliFiniteWindowDiagonalBridgeToEventFlow x =
      arzelaAscoliFiniteWindowDiagonalBridgeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      arzelaAscoliFiniteWindowDiagonalBridgeFromEventFlow
          (arzelaAscoliFiniteWindowDiagonalBridgeToEventFlow x) =
        arzelaAscoliFiniteWindowDiagonalBridgeFromEventFlow
          (arzelaAscoliFiniteWindowDiagonalBridgeToEventFlow y) :=
    congrArg arzelaAscoliFiniteWindowDiagonalBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ArzelaAscoliFiniteWindowDiagonalBridgeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ArzelaAscoliFiniteWindowDiagonalBridgeTasteGate_single_carrier_alignment_round_trip y)))

instance arzelaAscoliFiniteWindowDiagonalBridgeBHistCarrier :
    BHistCarrier ArzelaAscoliFiniteWindowDiagonalBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := arzelaAscoliFiniteWindowDiagonalBridgeToEventFlow
  fromEventFlow := arzelaAscoliFiniteWindowDiagonalBridgeFromEventFlow

instance arzelaAscoliFiniteWindowDiagonalBridgeChapterTasteGate :
    ChapterTasteGate ArzelaAscoliFiniteWindowDiagonalBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      arzelaAscoliFiniteWindowDiagonalBridgeFromEventFlow
        (arzelaAscoliFiniteWindowDiagonalBridgeToEventFlow x) = some x
    exact ArzelaAscoliFiniteWindowDiagonalBridgeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ArzelaAscoliFiniteWindowDiagonalBridgeTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem ArzelaAscoliFiniteWindowDiagonalBridgeTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ArzelaAscoliFiniteWindowDiagonalBridgeUp) ∧
      Nonempty (BHistCarrier ArzelaAscoliFiniteWindowDiagonalBridgeUp) ∧
      (∀ h : BHist,
        arzelaAscoliFiniteWindowDiagonalBridgeDecodeBHist
          (arzelaAscoliFiniteWindowDiagonalBridgeEncodeBHist h) = h) ∧
      arzelaAscoliFiniteWindowDiagonalBridgeEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨arzelaAscoliFiniteWindowDiagonalBridgeChapterTasteGate⟩,
      ⟨arzelaAscoliFiniteWindowDiagonalBridgeBHistCarrier⟩,
      ArzelaAscoliFiniteWindowDiagonalBridgeTasteGate_single_carrier_alignment_decode_encode,
      rfl⟩

end BEDC.Derived.ArzelaAscoliFiniteWindowDiagonalBridgeUp
