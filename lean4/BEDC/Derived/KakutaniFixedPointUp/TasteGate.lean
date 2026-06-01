import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KakutaniFixedPointUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KakutaniFixedPointUp : Type where
  | mk (D G V S F H C P N : BHist) : KakutaniFixedPointUp
  deriving DecidableEq

def kakutaniFixedPointEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kakutaniFixedPointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kakutaniFixedPointEncodeBHist h

def kakutaniFixedPointDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kakutaniFixedPointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kakutaniFixedPointDecodeBHist tail)

private theorem KakutaniFixedPointTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, kakutaniFixedPointDecodeBHist (kakutaniFixedPointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kakutaniFixedPointFields : KakutaniFixedPointUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KakutaniFixedPointUp.mk D G V S F H C P N => [D, G, V, S, F, H, C, P, N]

def kakutaniFixedPointToEventFlow : KakutaniFixedPointUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (kakutaniFixedPointFields x).map kakutaniFixedPointEncodeBHist

private def kakutaniFixedPointEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kakutaniFixedPointEventAt index rest

def kakutaniFixedPointFromEventFlow (ef : EventFlow) : Option KakutaniFixedPointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (KakutaniFixedPointUp.mk
      (kakutaniFixedPointDecodeBHist (kakutaniFixedPointEventAt 0 ef))
      (kakutaniFixedPointDecodeBHist (kakutaniFixedPointEventAt 1 ef))
      (kakutaniFixedPointDecodeBHist (kakutaniFixedPointEventAt 2 ef))
      (kakutaniFixedPointDecodeBHist (kakutaniFixedPointEventAt 3 ef))
      (kakutaniFixedPointDecodeBHist (kakutaniFixedPointEventAt 4 ef))
      (kakutaniFixedPointDecodeBHist (kakutaniFixedPointEventAt 5 ef))
      (kakutaniFixedPointDecodeBHist (kakutaniFixedPointEventAt 6 ef))
      (kakutaniFixedPointDecodeBHist (kakutaniFixedPointEventAt 7 ef))
      (kakutaniFixedPointDecodeBHist (kakutaniFixedPointEventAt 8 ef)))

private theorem KakutaniFixedPointTasteGate_single_carrier_alignment_round_trip
    (x : KakutaniFixedPointUp) :
    kakutaniFixedPointFromEventFlow (kakutaniFixedPointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D G V S F H C P N =>
      change
        some
          (KakutaniFixedPointUp.mk
            (kakutaniFixedPointDecodeBHist (kakutaniFixedPointEncodeBHist D))
            (kakutaniFixedPointDecodeBHist (kakutaniFixedPointEncodeBHist G))
            (kakutaniFixedPointDecodeBHist (kakutaniFixedPointEncodeBHist V))
            (kakutaniFixedPointDecodeBHist (kakutaniFixedPointEncodeBHist S))
            (kakutaniFixedPointDecodeBHist (kakutaniFixedPointEncodeBHist F))
            (kakutaniFixedPointDecodeBHist (kakutaniFixedPointEncodeBHist H))
            (kakutaniFixedPointDecodeBHist (kakutaniFixedPointEncodeBHist C))
            (kakutaniFixedPointDecodeBHist (kakutaniFixedPointEncodeBHist P))
            (kakutaniFixedPointDecodeBHist (kakutaniFixedPointEncodeBHist N))) =
          some (KakutaniFixedPointUp.mk D G V S F H C P N)
      rw [KakutaniFixedPointTasteGate_single_carrier_alignment_decode_encode D,
        KakutaniFixedPointTasteGate_single_carrier_alignment_decode_encode G,
        KakutaniFixedPointTasteGate_single_carrier_alignment_decode_encode V,
        KakutaniFixedPointTasteGate_single_carrier_alignment_decode_encode S,
        KakutaniFixedPointTasteGate_single_carrier_alignment_decode_encode F,
        KakutaniFixedPointTasteGate_single_carrier_alignment_decode_encode H,
        KakutaniFixedPointTasteGate_single_carrier_alignment_decode_encode C,
        KakutaniFixedPointTasteGate_single_carrier_alignment_decode_encode P,
        KakutaniFixedPointTasteGate_single_carrier_alignment_decode_encode N]

private theorem KakutaniFixedPointTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : KakutaniFixedPointUp} :
    kakutaniFixedPointToEventFlow x = kakutaniFixedPointToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kakutaniFixedPointFromEventFlow (kakutaniFixedPointToEventFlow x) =
        kakutaniFixedPointFromEventFlow (kakutaniFixedPointToEventFlow y) :=
    congrArg kakutaniFixedPointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (KakutaniFixedPointTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (KakutaniFixedPointTasteGate_single_carrier_alignment_round_trip y)))

instance kakutaniFixedPointBHistCarrier : BHistCarrier KakutaniFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kakutaniFixedPointToEventFlow
  fromEventFlow := kakutaniFixedPointFromEventFlow

instance kakutaniFixedPointChapterTasteGate : ChapterTasteGate KakutaniFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kakutaniFixedPointFromEventFlow (kakutaniFixedPointToEventFlow x) = some x
    exact KakutaniFixedPointTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (KakutaniFixedPointTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def KakutaniFixedPointTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate KakutaniFixedPointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kakutaniFixedPointChapterTasteGate

theorem KakutaniFixedPointTasteGate_single_carrier_alignment :
    (∀ h : BHist, kakutaniFixedPointDecodeBHist (kakutaniFixedPointEncodeBHist h) = h) ∧
      (∀ x : KakutaniFixedPointUp,
        kakutaniFixedPointFromEventFlow (kakutaniFixedPointToEventFlow x) = some x) ∧
        (∀ x y : KakutaniFixedPointUp,
          kakutaniFixedPointToEventFlow x = kakutaniFixedPointToEventFlow y → x = y) ∧
          kakutaniFixedPointEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨KakutaniFixedPointTasteGate_single_carrier_alignment_decode_encode,
      KakutaniFixedPointTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        KakutaniFixedPointTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.KakutaniFixedPointUp
