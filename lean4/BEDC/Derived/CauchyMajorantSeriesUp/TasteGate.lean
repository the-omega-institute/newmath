import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyMajorantSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyMajorantSeriesUp : Type where
  | mk (A D S R B E H C P N : BHist) : CauchyMajorantSeriesUp
  deriving DecidableEq

def cauchyMajorantSeriesEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyMajorantSeriesEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyMajorantSeriesEncodeBHist h

def cauchyMajorantSeriesDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyMajorantSeriesDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyMajorantSeriesDecodeBHist tail)

private theorem CauchyMajorantSeriesUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyMajorantSeriesFields : CauchyMajorantSeriesUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyMajorantSeriesUp.mk A D S R B E H C P N => [A, D, S, R, B, E, H, C, P, N]

def cauchyMajorantSeriesToEventFlow : CauchyMajorantSeriesUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyMajorantSeriesFields x).map cauchyMajorantSeriesEncodeBHist

private def cauchyMajorantSeriesEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyMajorantSeriesEventAt index rest

def cauchyMajorantSeriesFromEventFlow (ef : EventFlow) :
    Option CauchyMajorantSeriesUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyMajorantSeriesUp.mk
      (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEventAt 0 ef))
      (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEventAt 1 ef))
      (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEventAt 2 ef))
      (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEventAt 3 ef))
      (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEventAt 4 ef))
      (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEventAt 5 ef))
      (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEventAt 6 ef))
      (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEventAt 7 ef))
      (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEventAt 8 ef))
      (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEventAt 9 ef)))

private theorem CauchyMajorantSeriesUpTasteGate_single_carrier_alignment_round_trip
    (x : CauchyMajorantSeriesUp) :
    cauchyMajorantSeriesFromEventFlow (cauchyMajorantSeriesToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A D S R B E H C P N =>
      change
        some
          (CauchyMajorantSeriesUp.mk
            (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEncodeBHist A))
            (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEncodeBHist D))
            (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEncodeBHist S))
            (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEncodeBHist R))
            (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEncodeBHist B))
            (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEncodeBHist E))
            (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEncodeBHist H))
            (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEncodeBHist C))
            (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEncodeBHist P))
            (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEncodeBHist N))) =
          some (CauchyMajorantSeriesUp.mk A D S R B E H C P N)
      rw [CauchyMajorantSeriesUpTasteGate_single_carrier_alignment_decode_encode A,
        CauchyMajorantSeriesUpTasteGate_single_carrier_alignment_decode_encode D,
        CauchyMajorantSeriesUpTasteGate_single_carrier_alignment_decode_encode S,
        CauchyMajorantSeriesUpTasteGate_single_carrier_alignment_decode_encode R,
        CauchyMajorantSeriesUpTasteGate_single_carrier_alignment_decode_encode B,
        CauchyMajorantSeriesUpTasteGate_single_carrier_alignment_decode_encode E,
        CauchyMajorantSeriesUpTasteGate_single_carrier_alignment_decode_encode H,
        CauchyMajorantSeriesUpTasteGate_single_carrier_alignment_decode_encode C,
        CauchyMajorantSeriesUpTasteGate_single_carrier_alignment_decode_encode P,
        CauchyMajorantSeriesUpTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyMajorantSeriesUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyMajorantSeriesUp} :
    cauchyMajorantSeriesToEventFlow x = cauchyMajorantSeriesToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyMajorantSeriesFromEventFlow (cauchyMajorantSeriesToEventFlow x) =
        cauchyMajorantSeriesFromEventFlow (cauchyMajorantSeriesToEventFlow y) :=
    congrArg cauchyMajorantSeriesFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyMajorantSeriesUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyMajorantSeriesUpTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyMajorantSeriesBHistCarrier : BHistCarrier CauchyMajorantSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyMajorantSeriesToEventFlow
  fromEventFlow := cauchyMajorantSeriesFromEventFlow

instance cauchyMajorantSeriesChapterTasteGate :
    ChapterTasteGate CauchyMajorantSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyMajorantSeriesFromEventFlow (cauchyMajorantSeriesToEventFlow x) = some x
    exact CauchyMajorantSeriesUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyMajorantSeriesUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def CauchyMajorantSeriesUpTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchyMajorantSeriesUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyMajorantSeriesChapterTasteGate

theorem CauchyMajorantSeriesUpTasteGate_single_carrier_alignment :
    ChapterTasteGate CauchyMajorantSeriesUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact cauchyMajorantSeriesChapterTasteGate

end BEDC.Derived.CauchyMajorantSeriesUp
