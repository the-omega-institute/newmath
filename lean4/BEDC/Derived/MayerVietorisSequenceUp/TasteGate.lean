import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MayerVietorisSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MayerVietorisSequenceUp : Type where
  | mk (X U V I A B C D Delta S H R P N : BHist) : MayerVietorisSequenceUp
  deriving DecidableEq

def mayerVietorisSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: mayerVietorisSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: mayerVietorisSequenceEncodeBHist h

def mayerVietorisSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (mayerVietorisSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (mayerVietorisSequenceDecodeBHist tail)

private theorem mayerVietorisSequence_decode_encode_bhist :
    ∀ h : BHist,
      mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def mayerVietorisSequenceToEventFlow : MayerVietorisSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MayerVietorisSequenceUp.mk X U V I A B C D Delta S H R P N =>
      [[BMark.b0],
        mayerVietorisSequenceEncodeBHist X,
        [BMark.b1, BMark.b0],
        mayerVietorisSequenceEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b0],
        mayerVietorisSequenceEncodeBHist V,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        mayerVietorisSequenceEncodeBHist I,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        mayerVietorisSequenceEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        mayerVietorisSequenceEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        mayerVietorisSequenceEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        mayerVietorisSequenceEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        mayerVietorisSequenceEncodeBHist Delta,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        mayerVietorisSequenceEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        mayerVietorisSequenceEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        mayerVietorisSequenceEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        mayerVietorisSequenceEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        mayerVietorisSequenceEncodeBHist N]

private def mayerVietorisSequenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => mayerVietorisSequenceEventAt index rest

def mayerVietorisSequenceFromEventFlow (ef : EventFlow) : Option MayerVietorisSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MayerVietorisSequenceUp.mk
      (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEventAt 1 ef))
      (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEventAt 3 ef))
      (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEventAt 5 ef))
      (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEventAt 7 ef))
      (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEventAt 9 ef))
      (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEventAt 11 ef))
      (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEventAt 13 ef))
      (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEventAt 15 ef))
      (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEventAt 17 ef))
      (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEventAt 19 ef))
      (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEventAt 21 ef))
      (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEventAt 23 ef))
      (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEventAt 25 ef))
      (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEventAt 27 ef)))

private theorem mayerVietorisSequence_round_trip :
    ∀ x : MayerVietorisSequenceUp,
      mayerVietorisSequenceFromEventFlow (mayerVietorisSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X U V I A B C D Delta S H R P N =>
      change
        some
          (MayerVietorisSequenceUp.mk
            (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEncodeBHist X))
            (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEncodeBHist U))
            (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEncodeBHist V))
            (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEncodeBHist I))
            (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEncodeBHist A))
            (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEncodeBHist B))
            (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEncodeBHist C))
            (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEncodeBHist D))
            (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEncodeBHist Delta))
            (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEncodeBHist S))
            (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEncodeBHist H))
            (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEncodeBHist R))
            (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEncodeBHist P))
            (mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEncodeBHist N))) =
          some (MayerVietorisSequenceUp.mk X U V I A B C D Delta S H R P N)
      rw [mayerVietorisSequence_decode_encode_bhist X,
        mayerVietorisSequence_decode_encode_bhist U,
        mayerVietorisSequence_decode_encode_bhist V,
        mayerVietorisSequence_decode_encode_bhist I,
        mayerVietorisSequence_decode_encode_bhist A,
        mayerVietorisSequence_decode_encode_bhist B,
        mayerVietorisSequence_decode_encode_bhist C,
        mayerVietorisSequence_decode_encode_bhist D,
        mayerVietorisSequence_decode_encode_bhist Delta,
        mayerVietorisSequence_decode_encode_bhist S,
        mayerVietorisSequence_decode_encode_bhist H,
        mayerVietorisSequence_decode_encode_bhist R,
        mayerVietorisSequence_decode_encode_bhist P,
        mayerVietorisSequence_decode_encode_bhist N]

private theorem mayerVietorisSequenceToEventFlow_injective {x y : MayerVietorisSequenceUp} :
    mayerVietorisSequenceToEventFlow x = mayerVietorisSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      mayerVietorisSequenceFromEventFlow (mayerVietorisSequenceToEventFlow x) =
        mayerVietorisSequenceFromEventFlow (mayerVietorisSequenceToEventFlow y) :=
    congrArg mayerVietorisSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (mayerVietorisSequence_round_trip x).symm
      (Eq.trans hread (mayerVietorisSequence_round_trip y)))

instance mayerVietorisSequenceBHistCarrier : BHistCarrier MayerVietorisSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := mayerVietorisSequenceToEventFlow
  fromEventFlow := mayerVietorisSequenceFromEventFlow

instance mayerVietorisSequenceChapterTasteGate :
    ChapterTasteGate MayerVietorisSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change mayerVietorisSequenceFromEventFlow (mayerVietorisSequenceToEventFlow x) = some x
    exact mayerVietorisSequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (mayerVietorisSequenceToEventFlow_injective heq)

theorem MayerVietorisSequenceTasteGate_single_carrier_alignment :
    (∃ carrier : BHistCarrier MayerVietorisSequenceUp,
        Nonempty (@ChapterTasteGate MayerVietorisSequenceUp carrier)) ∧
      (∀ h : BHist,
        mayerVietorisSequenceDecodeBHist (mayerVietorisSequenceEncodeBHist h) = h) ∧
      (∀ x : MayerVietorisSequenceUp,
        mayerVietorisSequenceFromEventFlow (mayerVietorisSequenceToEventFlow x) = some x) ∧
      mayerVietorisSequenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨mayerVietorisSequenceBHistCarrier, ⟨mayerVietorisSequenceChapterTasteGate⟩⟩
  · constructor
    · exact mayerVietorisSequence_decode_encode_bhist
    · constructor
      · exact mayerVietorisSequence_round_trip
      · rfl

end BEDC.Derived.MayerVietorisSequenceUp
