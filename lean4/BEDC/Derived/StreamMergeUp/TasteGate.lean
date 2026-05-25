import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StreamMergeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StreamMergeUp : Type where
  | mk : (S0 S1 sigma W0 W1 W H C P N : BHist) → StreamMergeUp

def streamMergeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: streamMergeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: streamMergeEncodeBHist h

def streamMergeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (streamMergeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (streamMergeDecodeBHist tail)

private theorem streamMergeDecode_encode_bhist :
    ∀ h : BHist, streamMergeDecodeBHist (streamMergeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def streamMergeToEventFlow : StreamMergeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | StreamMergeUp.mk S0 S1 sigma W0 W1 W H C P N =>
      [[BMark.b0],
        streamMergeEncodeBHist S0,
        [BMark.b1, BMark.b0],
        streamMergeEncodeBHist S1,
        [BMark.b1, BMark.b1, BMark.b0],
        streamMergeEncodeBHist sigma,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        streamMergeEncodeBHist W0,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        streamMergeEncodeBHist W1,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        streamMergeEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        streamMergeEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        streamMergeEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        streamMergeEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        streamMergeEncodeBHist N]

def streamMergeFromEventFlow : EventFlow → Option StreamMergeUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag0 :: S0 :: _tag1 :: S1 :: _tag2 :: sigma :: _tag3 :: W0 :: _tag4 ::
      W1 :: _tag5 :: W :: _tag6 :: H :: _tag7 :: C :: _tag8 :: P :: _tag9 :: N ::
      [] =>
      some (StreamMergeUp.mk
        (streamMergeDecodeBHist S0) (streamMergeDecodeBHist S1)
        (streamMergeDecodeBHist sigma) (streamMergeDecodeBHist W0)
        (streamMergeDecodeBHist W1) (streamMergeDecodeBHist W)
        (streamMergeDecodeBHist H) (streamMergeDecodeBHist C)
        (streamMergeDecodeBHist P) (streamMergeDecodeBHist N))
  | [] => none
  | _ :: [] => none
  | _ :: _ :: [] => none
  | _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
      [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
      _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
      _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
      _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
      _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
      _ :: _ :: _ :: _ :: _ :: _ :: _ => none

private theorem streamMerge_round_trip :
    ∀ x : StreamMergeUp,
      streamMergeFromEventFlow (streamMergeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S0 S1 sigma W0 W1 W H C P N =>
      change
        some
          (StreamMergeUp.mk
            (streamMergeDecodeBHist (streamMergeEncodeBHist S0))
            (streamMergeDecodeBHist (streamMergeEncodeBHist S1))
            (streamMergeDecodeBHist (streamMergeEncodeBHist sigma))
            (streamMergeDecodeBHist (streamMergeEncodeBHist W0))
            (streamMergeDecodeBHist (streamMergeEncodeBHist W1))
            (streamMergeDecodeBHist (streamMergeEncodeBHist W))
            (streamMergeDecodeBHist (streamMergeEncodeBHist H))
            (streamMergeDecodeBHist (streamMergeEncodeBHist C))
            (streamMergeDecodeBHist (streamMergeEncodeBHist P))
            (streamMergeDecodeBHist (streamMergeEncodeBHist N))) =
          some (StreamMergeUp.mk S0 S1 sigma W0 W1 W H C P N)
      rw [streamMergeDecode_encode_bhist S0,
        streamMergeDecode_encode_bhist S1,
        streamMergeDecode_encode_bhist sigma,
        streamMergeDecode_encode_bhist W0,
        streamMergeDecode_encode_bhist W1,
        streamMergeDecode_encode_bhist W,
        streamMergeDecode_encode_bhist H,
        streamMergeDecode_encode_bhist C,
        streamMergeDecode_encode_bhist P,
        streamMergeDecode_encode_bhist N]

private theorem streamMergeToEventFlow_injective {x y : StreamMergeUp} :
    streamMergeToEventFlow x = streamMergeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      streamMergeFromEventFlow (streamMergeToEventFlow x) =
        streamMergeFromEventFlow (streamMergeToEventFlow y) :=
    congrArg streamMergeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (streamMerge_round_trip x).symm
      (Eq.trans hread (streamMerge_round_trip y)))

instance streamMergeBHistCarrier : BHistCarrier StreamMergeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := streamMergeToEventFlow
  fromEventFlow := streamMergeFromEventFlow

instance streamMergeChapterTasteGate : ChapterTasteGate StreamMergeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change streamMergeFromEventFlow (streamMergeToEventFlow x) = some x
    exact streamMerge_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (streamMergeToEventFlow_injective heq)

def taste_gate : ChapterTasteGate StreamMergeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  streamMergeChapterTasteGate

theorem StreamMergeTasteGate_single_carrier_alignment :
    (∀ h : BHist, streamMergeDecodeBHist (streamMergeEncodeBHist h) = h) ∧
      (∀ x : StreamMergeUp,
        streamMergeFromEventFlow (streamMergeToEventFlow x) = some x) ∧
      (∀ x y : StreamMergeUp,
        streamMergeToEventFlow x = streamMergeToEventFlow y → x = y) ∧
      streamMergeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact streamMergeDecode_encode_bhist
  · constructor
    · exact streamMerge_round_trip
    · constructor
      · intro x y heq
        exact streamMergeToEventFlow_injective heq
      · rfl

end BEDC.Derived.StreamMergeUp
