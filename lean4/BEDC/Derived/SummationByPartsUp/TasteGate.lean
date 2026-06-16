import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SummationByPartsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SummationByPartsUp : Type where
  | mk (S A Delta P B T R D E H C Q N : BHist) : SummationByPartsUp
  deriving DecidableEq

def summationByPartsEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: summationByPartsEncodeBHist h
  | BHist.e1 h => BMark.b1 :: summationByPartsEncodeBHist h

def summationByPartsDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (summationByPartsDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (summationByPartsDecodeBHist tail)

private theorem SummationByPartsTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      summationByPartsDecodeBHist (summationByPartsEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def summationByPartsToEventFlow : SummationByPartsUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SummationByPartsUp.mk S A Delta P B T R D E H C Q N =>
      [summationByPartsEncodeBHist S,
        summationByPartsEncodeBHist A,
        summationByPartsEncodeBHist Delta,
        summationByPartsEncodeBHist P,
        summationByPartsEncodeBHist B,
        summationByPartsEncodeBHist T,
        summationByPartsEncodeBHist R,
        summationByPartsEncodeBHist D,
        summationByPartsEncodeBHist E,
        summationByPartsEncodeBHist H,
        summationByPartsEncodeBHist C,
        summationByPartsEncodeBHist Q,
        summationByPartsEncodeBHist N]

private def summationByPartsEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => summationByPartsEventAt index rest

def summationByPartsDecodeFields (ef : EventFlow) : SummationByPartsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  SummationByPartsUp.mk
    (summationByPartsDecodeBHist (summationByPartsEventAt 0 ef))
    (summationByPartsDecodeBHist (summationByPartsEventAt 1 ef))
    (summationByPartsDecodeBHist (summationByPartsEventAt 2 ef))
    (summationByPartsDecodeBHist (summationByPartsEventAt 3 ef))
    (summationByPartsDecodeBHist (summationByPartsEventAt 4 ef))
    (summationByPartsDecodeBHist (summationByPartsEventAt 5 ef))
    (summationByPartsDecodeBHist (summationByPartsEventAt 6 ef))
    (summationByPartsDecodeBHist (summationByPartsEventAt 7 ef))
    (summationByPartsDecodeBHist (summationByPartsEventAt 8 ef))
    (summationByPartsDecodeBHist (summationByPartsEventAt 9 ef))
    (summationByPartsDecodeBHist (summationByPartsEventAt 10 ef))
    (summationByPartsDecodeBHist (summationByPartsEventAt 11 ef))
    (summationByPartsDecodeBHist (summationByPartsEventAt 12 ef))

def summationByPartsFromEventFlow : EventFlow -> Option SummationByPartsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef => some (summationByPartsDecodeFields ef)

private theorem SummationByPartsTasteGate_single_carrier_alignment_round_trip
    (x : SummationByPartsUp) :
    summationByPartsFromEventFlow (summationByPartsToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S A Delta P B T R D E H C Q N =>
      change
        some
            (SummationByPartsUp.mk
              (summationByPartsDecodeBHist (summationByPartsEncodeBHist S))
              (summationByPartsDecodeBHist (summationByPartsEncodeBHist A))
              (summationByPartsDecodeBHist (summationByPartsEncodeBHist Delta))
              (summationByPartsDecodeBHist (summationByPartsEncodeBHist P))
              (summationByPartsDecodeBHist (summationByPartsEncodeBHist B))
              (summationByPartsDecodeBHist (summationByPartsEncodeBHist T))
              (summationByPartsDecodeBHist (summationByPartsEncodeBHist R))
              (summationByPartsDecodeBHist (summationByPartsEncodeBHist D))
              (summationByPartsDecodeBHist (summationByPartsEncodeBHist E))
              (summationByPartsDecodeBHist (summationByPartsEncodeBHist H))
              (summationByPartsDecodeBHist (summationByPartsEncodeBHist C))
              (summationByPartsDecodeBHist (summationByPartsEncodeBHist Q))
              (summationByPartsDecodeBHist (summationByPartsEncodeBHist N))) =
          some (SummationByPartsUp.mk S A Delta P B T R D E H C Q N)
      rw [SummationByPartsTasteGate_single_carrier_alignment_decode_encode S,
        SummationByPartsTasteGate_single_carrier_alignment_decode_encode A,
        SummationByPartsTasteGate_single_carrier_alignment_decode_encode Delta,
        SummationByPartsTasteGate_single_carrier_alignment_decode_encode P,
        SummationByPartsTasteGate_single_carrier_alignment_decode_encode B,
        SummationByPartsTasteGate_single_carrier_alignment_decode_encode T,
        SummationByPartsTasteGate_single_carrier_alignment_decode_encode R,
        SummationByPartsTasteGate_single_carrier_alignment_decode_encode D,
        SummationByPartsTasteGate_single_carrier_alignment_decode_encode E,
        SummationByPartsTasteGate_single_carrier_alignment_decode_encode H,
        SummationByPartsTasteGate_single_carrier_alignment_decode_encode C,
        SummationByPartsTasteGate_single_carrier_alignment_decode_encode Q,
        SummationByPartsTasteGate_single_carrier_alignment_decode_encode N]

private theorem SummationByPartsTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SummationByPartsUp} :
    summationByPartsToEventFlow x = summationByPartsToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      summationByPartsFromEventFlow (summationByPartsToEventFlow x) =
        summationByPartsFromEventFlow (summationByPartsToEventFlow y) :=
    congrArg summationByPartsFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SummationByPartsTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SummationByPartsTasteGate_single_carrier_alignment_round_trip y)))

instance summationByPartsBHistCarrier : BHistCarrier SummationByPartsUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := summationByPartsToEventFlow
  fromEventFlow := summationByPartsFromEventFlow

instance summationByPartsChapterTasteGate : ChapterTasteGate SummationByPartsUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change summationByPartsFromEventFlow (summationByPartsToEventFlow x) = some x
    exact SummationByPartsTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SummationByPartsTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem SummationByPartsTasteGate_single_carrier_alignment :
    (forall h : BHist, summationByPartsDecodeBHist (summationByPartsEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SummationByPartsUp) ∧
        Nonempty (ChapterTasteGate SummationByPartsUp) ∧
          summationByPartsEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨SummationByPartsTasteGate_single_carrier_alignment_decode_encode,
      ⟨summationByPartsBHistCarrier⟩,
      ⟨summationByPartsChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.SummationByPartsUp
