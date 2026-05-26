import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedChoiceSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedChoiceSequenceUp : Type where
  | mk (Q S W A D M R E H C P N : BHist) : LocatedChoiceSequenceUp
  deriving DecidableEq

def locatedChoiceSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedChoiceSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedChoiceSequenceEncodeBHist h

def locatedChoiceSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedChoiceSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedChoiceSequenceDecodeBHist tail)

private theorem locatedChoiceSequence_decode_encode :
    ∀ h : BHist, locatedChoiceSequenceDecodeBHist (locatedChoiceSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedChoiceSequenceToEventFlow : LocatedChoiceSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedChoiceSequenceUp.mk Q S W A D M R E H C P N =>
      [locatedChoiceSequenceEncodeBHist Q, locatedChoiceSequenceEncodeBHist S,
        locatedChoiceSequenceEncodeBHist W, locatedChoiceSequenceEncodeBHist A,
        locatedChoiceSequenceEncodeBHist D, locatedChoiceSequenceEncodeBHist M,
        locatedChoiceSequenceEncodeBHist R, locatedChoiceSequenceEncodeBHist E,
        locatedChoiceSequenceEncodeBHist H, locatedChoiceSequenceEncodeBHist C,
        locatedChoiceSequenceEncodeBHist P, locatedChoiceSequenceEncodeBHist N]

def locatedChoiceSequenceFromEventFlow (flow : EventFlow) : Option LocatedChoiceSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match flow with
  | [] => none
  | Q :: rest =>
      match rest with
      | [] => none
      | S :: rest =>
          match rest with
          | [] => none
          | W :: rest =>
              match rest with
              | [] => none
              | A :: rest =>
                  match rest with
                  | [] => none
                  | D :: rest =>
                      match rest with
                      | [] => none
                      | M :: rest =>
                          match rest with
                          | [] => none
                          | R :: rest =>
                              match rest with
                              | [] => none
                              | E :: rest =>
                                  match rest with
                                  | [] => none
                                  | H :: rest =>
                                      match rest with
                                      | [] => none
                                      | C :: rest =>
                                          match rest with
                                          | [] => none
                                          | P :: rest =>
                                              match rest with
                                              | [] => none
                                              | N :: rest =>
                                                  match rest with
                                                  | [] =>
                                                      some
                                                        (LocatedChoiceSequenceUp.mk
                                                          (locatedChoiceSequenceDecodeBHist Q)
                                                          (locatedChoiceSequenceDecodeBHist S)
                                                          (locatedChoiceSequenceDecodeBHist W)
                                                          (locatedChoiceSequenceDecodeBHist A)
                                                          (locatedChoiceSequenceDecodeBHist D)
                                                          (locatedChoiceSequenceDecodeBHist M)
                                                          (locatedChoiceSequenceDecodeBHist R)
                                                          (locatedChoiceSequenceDecodeBHist E)
                                                          (locatedChoiceSequenceDecodeBHist H)
                                                          (locatedChoiceSequenceDecodeBHist C)
                                                          (locatedChoiceSequenceDecodeBHist P)
                                                          (locatedChoiceSequenceDecodeBHist N))
                                                  | _ :: _ => none

private theorem locatedChoiceSequence_round_trip :
    ∀ x : LocatedChoiceSequenceUp,
      locatedChoiceSequenceFromEventFlow (locatedChoiceSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q S W A D M R E H C P N =>
      rw [locatedChoiceSequenceToEventFlow, locatedChoiceSequenceFromEventFlow,
        locatedChoiceSequence_decode_encode Q, locatedChoiceSequence_decode_encode S,
        locatedChoiceSequence_decode_encode W, locatedChoiceSequence_decode_encode A,
        locatedChoiceSequence_decode_encode D, locatedChoiceSequence_decode_encode M,
        locatedChoiceSequence_decode_encode R, locatedChoiceSequence_decode_encode E,
        locatedChoiceSequence_decode_encode H, locatedChoiceSequence_decode_encode C,
        locatedChoiceSequence_decode_encode P, locatedChoiceSequence_decode_encode N]

private theorem locatedChoiceSequenceToEventFlow_injective
    {x y : LocatedChoiceSequenceUp} :
    locatedChoiceSequenceToEventFlow x = locatedChoiceSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedChoiceSequenceFromEventFlow (locatedChoiceSequenceToEventFlow x) =
        locatedChoiceSequenceFromEventFlow (locatedChoiceSequenceToEventFlow y) :=
    congrArg locatedChoiceSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedChoiceSequence_round_trip x).symm
      (Eq.trans hread (locatedChoiceSequence_round_trip y)))

instance locatedChoiceSequenceBHistCarrier : BHistCarrier LocatedChoiceSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedChoiceSequenceToEventFlow
  fromEventFlow := locatedChoiceSequenceFromEventFlow

instance locatedChoiceSequenceChapterTasteGate :
    ChapterTasteGate LocatedChoiceSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedChoiceSequenceFromEventFlow (locatedChoiceSequenceToEventFlow x) = some x
    exact locatedChoiceSequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedChoiceSequenceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedChoiceSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedChoiceSequenceChapterTasteGate

theorem LocatedChoiceSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedChoiceSequenceDecodeBHist (locatedChoiceSequenceEncodeBHist h) = h) ∧
      (∀ x : LocatedChoiceSequenceUp,
        locatedChoiceSequenceFromEventFlow (locatedChoiceSequenceToEventFlow x) = some x) ∧
      (∀ x y : LocatedChoiceSequenceUp,
        locatedChoiceSequenceToEventFlow x = locatedChoiceSequenceToEventFlow y → x = y) ∧
      locatedChoiceSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨locatedChoiceSequence_decode_encode,
      locatedChoiceSequence_round_trip,
      fun _ _ heq => locatedChoiceSequenceToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.LocatedChoiceSequenceUp
