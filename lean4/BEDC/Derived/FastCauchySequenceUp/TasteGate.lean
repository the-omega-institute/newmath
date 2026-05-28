import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FastCauchySequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FastCauchySequenceUp : Type where
  | mk (D S M R H C P N : BHist) : FastCauchySequenceUp
  deriving DecidableEq

def fastCauchySequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fastCauchySequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fastCauchySequenceEncodeBHist h

def fastCauchySequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fastCauchySequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fastCauchySequenceDecodeBHist tail)

private theorem fastCauchySequence_decode_encode_bhist :
    ∀ h : BHist, fastCauchySequenceDecodeBHist (fastCauchySequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fastCauchySequenceFields : FastCauchySequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FastCauchySequenceUp.mk D S M R H C P N => [D, S, M, R, H, C, P, N]

def fastCauchySequenceToEventFlow : FastCauchySequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (fastCauchySequenceFields x).map fastCauchySequenceEncodeBHist

private def fastCauchySequenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => fastCauchySequenceEventAtDefault index rest

def fastCauchySequenceFromEventFlow (ef : EventFlow) : Option FastCauchySequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FastCauchySequenceUp.mk
      (fastCauchySequenceDecodeBHist (fastCauchySequenceEventAtDefault 0 ef))
      (fastCauchySequenceDecodeBHist (fastCauchySequenceEventAtDefault 1 ef))
      (fastCauchySequenceDecodeBHist (fastCauchySequenceEventAtDefault 2 ef))
      (fastCauchySequenceDecodeBHist (fastCauchySequenceEventAtDefault 3 ef))
      (fastCauchySequenceDecodeBHist (fastCauchySequenceEventAtDefault 4 ef))
      (fastCauchySequenceDecodeBHist (fastCauchySequenceEventAtDefault 5 ef))
      (fastCauchySequenceDecodeBHist (fastCauchySequenceEventAtDefault 6 ef))
      (fastCauchySequenceDecodeBHist (fastCauchySequenceEventAtDefault 7 ef)))

private theorem fastCauchySequence_round_trip :
    ∀ x : FastCauchySequenceUp,
      fastCauchySequenceFromEventFlow (fastCauchySequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S M R H C P N =>
      change
        some
          (FastCauchySequenceUp.mk
            (fastCauchySequenceDecodeBHist (fastCauchySequenceEncodeBHist D))
            (fastCauchySequenceDecodeBHist (fastCauchySequenceEncodeBHist S))
            (fastCauchySequenceDecodeBHist (fastCauchySequenceEncodeBHist M))
            (fastCauchySequenceDecodeBHist (fastCauchySequenceEncodeBHist R))
            (fastCauchySequenceDecodeBHist (fastCauchySequenceEncodeBHist H))
            (fastCauchySequenceDecodeBHist (fastCauchySequenceEncodeBHist C))
            (fastCauchySequenceDecodeBHist (fastCauchySequenceEncodeBHist P))
            (fastCauchySequenceDecodeBHist (fastCauchySequenceEncodeBHist N))) =
          some (FastCauchySequenceUp.mk D S M R H C P N)
      rw [fastCauchySequence_decode_encode_bhist D,
        fastCauchySequence_decode_encode_bhist S,
        fastCauchySequence_decode_encode_bhist M,
        fastCauchySequence_decode_encode_bhist R,
        fastCauchySequence_decode_encode_bhist H,
        fastCauchySequence_decode_encode_bhist C,
        fastCauchySequence_decode_encode_bhist P,
        fastCauchySequence_decode_encode_bhist N]

private theorem fastCauchySequenceToEventFlow_injective
    {x y : FastCauchySequenceUp} :
    fastCauchySequenceToEventFlow x = fastCauchySequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fastCauchySequenceFromEventFlow (fastCauchySequenceToEventFlow x) =
        fastCauchySequenceFromEventFlow (fastCauchySequenceToEventFlow y) :=
    congrArg fastCauchySequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fastCauchySequence_round_trip x).symm
      (Eq.trans hread (fastCauchySequence_round_trip y)))

instance fastCauchySequenceBHistCarrier : BHistCarrier FastCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fastCauchySequenceToEventFlow
  fromEventFlow := fastCauchySequenceFromEventFlow

instance fastCauchySequenceChapterTasteGate :
    ChapterTasteGate FastCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fastCauchySequenceFromEventFlow (fastCauchySequenceToEventFlow x) = some x
    exact fastCauchySequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fastCauchySequenceToEventFlow_injective heq)

theorem FastCauchySequenceTasteGate_single_carrier_alignment :
    ChapterTasteGate FastCauchySequenceUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact fastCauchySequenceChapterTasteGate

end BEDC.Derived.FastCauchySequenceUp
