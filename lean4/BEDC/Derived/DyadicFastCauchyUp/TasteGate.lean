import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicFastCauchyUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicFastCauchyUp : Type where
  | mk (D S M R E H C P N : BHist) : DyadicFastCauchyUp
  deriving DecidableEq

def dyadicFastCauchyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicFastCauchyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicFastCauchyEncodeBHist h

def dyadicFastCauchyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicFastCauchyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicFastCauchyDecodeBHist tail)

private theorem DyadicFastCauchyTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, dyadicFastCauchyDecodeBHist (dyadicFastCauchyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicFastCauchyFields : DyadicFastCauchyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicFastCauchyUp.mk D S M R E H C P N => [D, S, M, R, E, H, C, P, N]

def dyadicFastCauchyToEventFlow : DyadicFastCauchyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicFastCauchyFields x).map dyadicFastCauchyEncodeBHist

private def DyadicFastCauchyTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      DyadicFastCauchyTasteGate_single_carrier_alignment_eventAt index rest

def dyadicFastCauchyDecodeFields (ef : EventFlow) : DyadicFastCauchyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  DyadicFastCauchyUp.mk
    (dyadicFastCauchyDecodeBHist
      (DyadicFastCauchyTasteGate_single_carrier_alignment_eventAt 0 ef))
    (dyadicFastCauchyDecodeBHist
      (DyadicFastCauchyTasteGate_single_carrier_alignment_eventAt 1 ef))
    (dyadicFastCauchyDecodeBHist
      (DyadicFastCauchyTasteGate_single_carrier_alignment_eventAt 2 ef))
    (dyadicFastCauchyDecodeBHist
      (DyadicFastCauchyTasteGate_single_carrier_alignment_eventAt 3 ef))
    (dyadicFastCauchyDecodeBHist
      (DyadicFastCauchyTasteGate_single_carrier_alignment_eventAt 4 ef))
    (dyadicFastCauchyDecodeBHist
      (DyadicFastCauchyTasteGate_single_carrier_alignment_eventAt 5 ef))
    (dyadicFastCauchyDecodeBHist
      (DyadicFastCauchyTasteGate_single_carrier_alignment_eventAt 6 ef))
    (dyadicFastCauchyDecodeBHist
      (DyadicFastCauchyTasteGate_single_carrier_alignment_eventAt 7 ef))
    (dyadicFastCauchyDecodeBHist
      (DyadicFastCauchyTasteGate_single_carrier_alignment_eventAt 8 ef))

def dyadicFastCauchyFromEventFlow (ef : EventFlow) : Option DyadicFastCauchyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some (dyadicFastCauchyDecodeFields ef)

private theorem DyadicFastCauchyTasteGate_single_carrier_alignment_round_trip
    (x : DyadicFastCauchyUp) :
    dyadicFastCauchyFromEventFlow (dyadicFastCauchyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D S M R E H C P N =>
      change
        some
          (DyadicFastCauchyUp.mk
            (dyadicFastCauchyDecodeBHist (dyadicFastCauchyEncodeBHist D))
            (dyadicFastCauchyDecodeBHist (dyadicFastCauchyEncodeBHist S))
            (dyadicFastCauchyDecodeBHist (dyadicFastCauchyEncodeBHist M))
            (dyadicFastCauchyDecodeBHist (dyadicFastCauchyEncodeBHist R))
            (dyadicFastCauchyDecodeBHist (dyadicFastCauchyEncodeBHist E))
            (dyadicFastCauchyDecodeBHist (dyadicFastCauchyEncodeBHist H))
            (dyadicFastCauchyDecodeBHist (dyadicFastCauchyEncodeBHist C))
            (dyadicFastCauchyDecodeBHist (dyadicFastCauchyEncodeBHist P))
            (dyadicFastCauchyDecodeBHist (dyadicFastCauchyEncodeBHist N))) =
          some (DyadicFastCauchyUp.mk D S M R E H C P N)
      rw [DyadicFastCauchyTasteGate_single_carrier_alignment_decode_encode D,
        DyadicFastCauchyTasteGate_single_carrier_alignment_decode_encode S,
        DyadicFastCauchyTasteGate_single_carrier_alignment_decode_encode M,
        DyadicFastCauchyTasteGate_single_carrier_alignment_decode_encode R,
        DyadicFastCauchyTasteGate_single_carrier_alignment_decode_encode E,
        DyadicFastCauchyTasteGate_single_carrier_alignment_decode_encode H,
        DyadicFastCauchyTasteGate_single_carrier_alignment_decode_encode C,
        DyadicFastCauchyTasteGate_single_carrier_alignment_decode_encode P,
        DyadicFastCauchyTasteGate_single_carrier_alignment_decode_encode N]

private theorem DyadicFastCauchyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicFastCauchyUp} :
    dyadicFastCauchyToEventFlow x = dyadicFastCauchyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicFastCauchyFromEventFlow (dyadicFastCauchyToEventFlow x) =
        dyadicFastCauchyFromEventFlow (dyadicFastCauchyToEventFlow y) :=
    congrArg dyadicFastCauchyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicFastCauchyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicFastCauchyTasteGate_single_carrier_alignment_round_trip y)))

instance dyadicFastCauchyBHistCarrier : BHistCarrier DyadicFastCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicFastCauchyToEventFlow
  fromEventFlow := dyadicFastCauchyFromEventFlow

instance dyadicFastCauchyChapterTasteGate : ChapterTasteGate DyadicFastCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicFastCauchyFromEventFlow (dyadicFastCauchyToEventFlow x) = some x
    exact DyadicFastCauchyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicFastCauchyTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate DyadicFastCauchyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicFastCauchyChapterTasteGate

theorem DyadicFastCauchyTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicFastCauchyDecodeBHist (dyadicFastCauchyEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier DyadicFastCauchyUp) ∧
        Nonempty (ChapterTasteGate DyadicFastCauchyUp) ∧
          dyadicFastCauchyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨DyadicFastCauchyTasteGate_single_carrier_alignment_decode_encode,
      ⟨dyadicFastCauchyBHistCarrier⟩,
      ⟨dyadicFastCauchyChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.DyadicFastCauchyUp.TasteGate
