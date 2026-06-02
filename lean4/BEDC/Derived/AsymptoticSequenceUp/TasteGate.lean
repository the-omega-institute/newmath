import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

/-!
# AsymptoticSequenceUp TasteGate carrier.
-/

namespace BEDC.Derived.AsymptoticSequenceUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- AsymptoticSequence packet with the twelve displayed rows. -/
inductive AsymptoticSequenceUp : Type where
  | mk : (S T W M Q L E F H C P N : BHist) → AsymptoticSequenceUp
  deriving DecidableEq

def asymptoticSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: asymptoticSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: asymptoticSequenceEncodeBHist h

def asymptoticSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (asymptoticSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (asymptoticSequenceDecodeBHist tail)

private theorem AsymptoticSequenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, asymptoticSequenceDecodeBHist (asymptoticSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def asymptoticSequenceToEventFlow : AsymptoticSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AsymptoticSequenceUp.mk S T W M Q L E F H C P N =>
      [[BMark.b0],
        asymptoticSequenceEncodeBHist S,
        [BMark.b1, BMark.b0],
        asymptoticSequenceEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b0],
        asymptoticSequenceEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        asymptoticSequenceEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        asymptoticSequenceEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        asymptoticSequenceEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        asymptoticSequenceEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        asymptoticSequenceEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        asymptoticSequenceEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        asymptoticSequenceEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        asymptoticSequenceEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        asymptoticSequenceEncodeBHist N]

private def asymptoticSequenceDecodeRows :
    EventFlow → Option (List BHist)
  -- BEDC touchpoint anchor: BHist BMark
  | [] => some []
  | _tag :: rest0 =>
      match rest0 with
      | [] => none
      | row :: rest1 =>
          match asymptoticSequenceDecodeRows rest1 with
          | some rows => some (asymptoticSequenceDecodeBHist row :: rows)
          | none => none

private def asymptoticSequenceFromRows :
    List BHist → Option AsymptoticSequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | T :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | M :: rest3 =>
                  match rest3 with
                  | [] => none
                  | Q :: rest4 =>
                      match rest4 with
                      | [] => none
                      | L :: rest5 =>
                          match rest5 with
                          | [] => none
                          | E :: rest6 =>
                              match rest6 with
                              | [] => none
                              | F :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | H :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | C :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | P :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | N :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (AsymptoticSequenceUp.mk
                                                          S T W M Q L E F H C P N)
                                                  | _ :: _ => none

def asymptoticSequenceFromEventFlow : EventFlow → Option AsymptoticSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    match asymptoticSequenceDecodeRows ef with
    | some rows => asymptoticSequenceFromRows rows
    | none => none

private theorem AsymptoticSequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : AsymptoticSequenceUp,
      asymptoticSequenceFromEventFlow (asymptoticSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T W M Q L E F H C P N =>
      change
        some
          (AsymptoticSequenceUp.mk
            (asymptoticSequenceDecodeBHist (asymptoticSequenceEncodeBHist S))
            (asymptoticSequenceDecodeBHist (asymptoticSequenceEncodeBHist T))
            (asymptoticSequenceDecodeBHist (asymptoticSequenceEncodeBHist W))
            (asymptoticSequenceDecodeBHist (asymptoticSequenceEncodeBHist M))
            (asymptoticSequenceDecodeBHist (asymptoticSequenceEncodeBHist Q))
            (asymptoticSequenceDecodeBHist (asymptoticSequenceEncodeBHist L))
            (asymptoticSequenceDecodeBHist (asymptoticSequenceEncodeBHist E))
            (asymptoticSequenceDecodeBHist (asymptoticSequenceEncodeBHist F))
            (asymptoticSequenceDecodeBHist (asymptoticSequenceEncodeBHist H))
            (asymptoticSequenceDecodeBHist (asymptoticSequenceEncodeBHist C))
            (asymptoticSequenceDecodeBHist (asymptoticSequenceEncodeBHist P))
            (asymptoticSequenceDecodeBHist (asymptoticSequenceEncodeBHist N))) =
          some (AsymptoticSequenceUp.mk S T W M Q L E F H C P N)
      rw [AsymptoticSequenceTasteGate_single_carrier_alignment_decode_encode S,
        AsymptoticSequenceTasteGate_single_carrier_alignment_decode_encode T,
        AsymptoticSequenceTasteGate_single_carrier_alignment_decode_encode W,
        AsymptoticSequenceTasteGate_single_carrier_alignment_decode_encode M,
        AsymptoticSequenceTasteGate_single_carrier_alignment_decode_encode Q,
        AsymptoticSequenceTasteGate_single_carrier_alignment_decode_encode L,
        AsymptoticSequenceTasteGate_single_carrier_alignment_decode_encode E,
        AsymptoticSequenceTasteGate_single_carrier_alignment_decode_encode F,
        AsymptoticSequenceTasteGate_single_carrier_alignment_decode_encode H,
        AsymptoticSequenceTasteGate_single_carrier_alignment_decode_encode C,
        AsymptoticSequenceTasteGate_single_carrier_alignment_decode_encode P,
        AsymptoticSequenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem AsymptoticSequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AsymptoticSequenceUp} :
    asymptoticSequenceToEventFlow x = asymptoticSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      asymptoticSequenceFromEventFlow (asymptoticSequenceToEventFlow x) =
        asymptoticSequenceFromEventFlow (asymptoticSequenceToEventFlow y) :=
    congrArg asymptoticSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AsymptoticSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (AsymptoticSequenceTasteGate_single_carrier_alignment_round_trip y)))

instance asymptoticSequenceBHistCarrier : BHistCarrier AsymptoticSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := asymptoticSequenceToEventFlow
  fromEventFlow := asymptoticSequenceFromEventFlow

instance asymptoticSequenceChapterTasteGate :
    ChapterTasteGate AsymptoticSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change asymptoticSequenceFromEventFlow (asymptoticSequenceToEventFlow x) = some x
    exact AsymptoticSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (AsymptoticSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

/-- Public TasteGate object for the AsymptoticSequence carrier. -/
def taste_gate : ChapterTasteGate AsymptoticSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  asymptoticSequenceChapterTasteGate

theorem AsymptoticSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, asymptoticSequenceDecodeBHist (asymptoticSequenceEncodeBHist h) = h) ∧
      (∀ x : AsymptoticSequenceUp,
        asymptoticSequenceFromEventFlow (asymptoticSequenceToEventFlow x) = some x) ∧
      (∀ x y : AsymptoticSequenceUp,
        asymptoticSequenceToEventFlow x = asymptoticSequenceToEventFlow y → x = y) ∧
      asymptoticSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact AsymptoticSequenceTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact AsymptoticSequenceTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact AsymptoticSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.AsymptoticSequenceUp
