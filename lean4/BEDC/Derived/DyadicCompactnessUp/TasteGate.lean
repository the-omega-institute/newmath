import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicCompactnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicCompactnessUp : Type where
  | mk (L Q D M Z F S R E H C P N : BHist) : DyadicCompactnessUp
  deriving DecidableEq

def dyadicCompactnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicCompactnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicCompactnessEncodeBHist h

def dyadicCompactnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicCompactnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicCompactnessDecodeBHist tail)

private theorem DyadicCompactnessTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, dyadicCompactnessDecodeBHist (dyadicCompactnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicCompactnessFields : DyadicCompactnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicCompactnessUp.mk L Q D M Z F S R E H C P N => [L, Q, D, M, Z, F, S, R, E, H, C, P, N]

def dyadicCompactnessToEventFlow : DyadicCompactnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicCompactnessFields x).map dyadicCompactnessEncodeBHist

private def dyadicCompactnessEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicCompactnessEventAt index rest

def dyadicCompactnessFromEventFlow (ef : EventFlow) : Option DyadicCompactnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicCompactnessUp.mk
      (dyadicCompactnessDecodeBHist (dyadicCompactnessEventAt 0 ef))
      (dyadicCompactnessDecodeBHist (dyadicCompactnessEventAt 1 ef))
      (dyadicCompactnessDecodeBHist (dyadicCompactnessEventAt 2 ef))
      (dyadicCompactnessDecodeBHist (dyadicCompactnessEventAt 3 ef))
      (dyadicCompactnessDecodeBHist (dyadicCompactnessEventAt 4 ef))
      (dyadicCompactnessDecodeBHist (dyadicCompactnessEventAt 5 ef))
      (dyadicCompactnessDecodeBHist (dyadicCompactnessEventAt 6 ef))
      (dyadicCompactnessDecodeBHist (dyadicCompactnessEventAt 7 ef))
      (dyadicCompactnessDecodeBHist (dyadicCompactnessEventAt 8 ef))
      (dyadicCompactnessDecodeBHist (dyadicCompactnessEventAt 9 ef))
      (dyadicCompactnessDecodeBHist (dyadicCompactnessEventAt 10 ef))
      (dyadicCompactnessDecodeBHist (dyadicCompactnessEventAt 11 ef))
      (dyadicCompactnessDecodeBHist (dyadicCompactnessEventAt 12 ef)))

private theorem DyadicCompactnessTasteGate_single_carrier_alignment_round_trip
    (x : DyadicCompactnessUp) :
    dyadicCompactnessFromEventFlow (dyadicCompactnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L Q D M Z F S R E H C P N =>
      change
        some
          (DyadicCompactnessUp.mk
            (dyadicCompactnessDecodeBHist (dyadicCompactnessEncodeBHist L))
            (dyadicCompactnessDecodeBHist (dyadicCompactnessEncodeBHist Q))
            (dyadicCompactnessDecodeBHist (dyadicCompactnessEncodeBHist D))
            (dyadicCompactnessDecodeBHist (dyadicCompactnessEncodeBHist M))
            (dyadicCompactnessDecodeBHist (dyadicCompactnessEncodeBHist Z))
            (dyadicCompactnessDecodeBHist (dyadicCompactnessEncodeBHist F))
            (dyadicCompactnessDecodeBHist (dyadicCompactnessEncodeBHist S))
            (dyadicCompactnessDecodeBHist (dyadicCompactnessEncodeBHist R))
            (dyadicCompactnessDecodeBHist (dyadicCompactnessEncodeBHist E))
            (dyadicCompactnessDecodeBHist (dyadicCompactnessEncodeBHist H))
            (dyadicCompactnessDecodeBHist (dyadicCompactnessEncodeBHist C))
            (dyadicCompactnessDecodeBHist (dyadicCompactnessEncodeBHist P))
            (dyadicCompactnessDecodeBHist (dyadicCompactnessEncodeBHist N))) =
          some (DyadicCompactnessUp.mk L Q D M Z F S R E H C P N)
      rw [DyadicCompactnessTasteGate_single_carrier_alignment_decode_encode L,
        DyadicCompactnessTasteGate_single_carrier_alignment_decode_encode Q,
        DyadicCompactnessTasteGate_single_carrier_alignment_decode_encode D,
        DyadicCompactnessTasteGate_single_carrier_alignment_decode_encode M,
        DyadicCompactnessTasteGate_single_carrier_alignment_decode_encode Z,
        DyadicCompactnessTasteGate_single_carrier_alignment_decode_encode F,
        DyadicCompactnessTasteGate_single_carrier_alignment_decode_encode S,
        DyadicCompactnessTasteGate_single_carrier_alignment_decode_encode R,
        DyadicCompactnessTasteGate_single_carrier_alignment_decode_encode E,
        DyadicCompactnessTasteGate_single_carrier_alignment_decode_encode H,
        DyadicCompactnessTasteGate_single_carrier_alignment_decode_encode C,
        DyadicCompactnessTasteGate_single_carrier_alignment_decode_encode P,
        DyadicCompactnessTasteGate_single_carrier_alignment_decode_encode N]

private theorem DyadicCompactnessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicCompactnessUp} :
    dyadicCompactnessToEventFlow x = dyadicCompactnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicCompactnessFromEventFlow (dyadicCompactnessToEventFlow x) =
        dyadicCompactnessFromEventFlow (dyadicCompactnessToEventFlow y) :=
    congrArg dyadicCompactnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicCompactnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DyadicCompactnessTasteGate_single_carrier_alignment_round_trip y)))

instance dyadicCompactnessBHistCarrier : BHistCarrier DyadicCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicCompactnessToEventFlow
  fromEventFlow := dyadicCompactnessFromEventFlow

instance dyadicCompactnessChapterTasteGate : ChapterTasteGate DyadicCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicCompactnessFromEventFlow (dyadicCompactnessToEventFlow x) = some x
    exact DyadicCompactnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicCompactnessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem DyadicCompactnessTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicCompactnessDecodeBHist (dyadicCompactnessEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier DyadicCompactnessUp) ∧
        Nonempty (ChapterTasteGate DyadicCompactnessUp) ∧
          dyadicCompactnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨DyadicCompactnessTasteGate_single_carrier_alignment_decode_encode,
      ⟨dyadicCompactnessBHistCarrier⟩, ⟨dyadicCompactnessChapterTasteGate⟩, rfl⟩

end BEDC.Derived.DyadicCompactnessUp
