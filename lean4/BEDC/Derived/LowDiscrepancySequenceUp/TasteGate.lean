import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LowDiscrepancySequenceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LowDiscrepancySequenceUp : Type where
  | mk (P Q B D H C G N : BHist) : LowDiscrepancySequenceUp
  deriving DecidableEq

def lowDiscrepancySequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lowDiscrepancySequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lowDiscrepancySequenceEncodeBHist h

def lowDiscrepancySequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lowDiscrepancySequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lowDiscrepancySequenceDecodeBHist tail)

private theorem lowDiscrepancySequence_decode_encode_bhist :
    ∀ h : BHist, lowDiscrepancySequenceDecodeBHist
      (lowDiscrepancySequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lowDiscrepancySequenceFields : LowDiscrepancySequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LowDiscrepancySequenceUp.mk P Q B D H C G N => [P, Q, B, D, H, C, G, N]

def lowDiscrepancySequenceToEventFlow : LowDiscrepancySequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map lowDiscrepancySequenceEncodeBHist (lowDiscrepancySequenceFields x)

def lowDiscrepancySequenceFromEventFlow : EventFlow → Option LowDiscrepancySequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | P :: rest0 =>
      match rest0 with
      | [] => none
      | Q :: rest1 =>
          match rest1 with
          | [] => none
          | B :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | H :: rest4 =>
                      match rest4 with
                      | [] => none
                      | C :: rest5 =>
                          match rest5 with
                          | [] => none
                          | G :: rest6 =>
                              match rest6 with
                              | [] => none
                              | N :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (LowDiscrepancySequenceUp.mk
                                          (lowDiscrepancySequenceDecodeBHist P)
                                          (lowDiscrepancySequenceDecodeBHist Q)
                                          (lowDiscrepancySequenceDecodeBHist B)
                                          (lowDiscrepancySequenceDecodeBHist D)
                                          (lowDiscrepancySequenceDecodeBHist H)
                                          (lowDiscrepancySequenceDecodeBHist C)
                                          (lowDiscrepancySequenceDecodeBHist G)
                                          (lowDiscrepancySequenceDecodeBHist N))
                                  | _ :: _ => none

private theorem lowDiscrepancySequence_round_trip :
    ∀ x : LowDiscrepancySequenceUp,
      lowDiscrepancySequenceFromEventFlow
        (lowDiscrepancySequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk P Q B D H C G N =>
      change
        some
          (LowDiscrepancySequenceUp.mk
            (lowDiscrepancySequenceDecodeBHist
              (lowDiscrepancySequenceEncodeBHist P))
            (lowDiscrepancySequenceDecodeBHist
              (lowDiscrepancySequenceEncodeBHist Q))
            (lowDiscrepancySequenceDecodeBHist
              (lowDiscrepancySequenceEncodeBHist B))
            (lowDiscrepancySequenceDecodeBHist
              (lowDiscrepancySequenceEncodeBHist D))
            (lowDiscrepancySequenceDecodeBHist
              (lowDiscrepancySequenceEncodeBHist H))
            (lowDiscrepancySequenceDecodeBHist
              (lowDiscrepancySequenceEncodeBHist C))
            (lowDiscrepancySequenceDecodeBHist
              (lowDiscrepancySequenceEncodeBHist G))
            (lowDiscrepancySequenceDecodeBHist
              (lowDiscrepancySequenceEncodeBHist N))) =
          some (LowDiscrepancySequenceUp.mk P Q B D H C G N)
      rw [lowDiscrepancySequence_decode_encode_bhist P,
        lowDiscrepancySequence_decode_encode_bhist Q,
        lowDiscrepancySequence_decode_encode_bhist B,
        lowDiscrepancySequence_decode_encode_bhist D,
        lowDiscrepancySequence_decode_encode_bhist H,
        lowDiscrepancySequence_decode_encode_bhist C,
        lowDiscrepancySequence_decode_encode_bhist G,
        lowDiscrepancySequence_decode_encode_bhist N]

private theorem lowDiscrepancySequenceToEventFlow_injective
    {x y : LowDiscrepancySequenceUp} :
    lowDiscrepancySequenceToEventFlow x = lowDiscrepancySequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lowDiscrepancySequenceFromEventFlow (lowDiscrepancySequenceToEventFlow x) =
        lowDiscrepancySequenceFromEventFlow (lowDiscrepancySequenceToEventFlow y) :=
    congrArg lowDiscrepancySequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (lowDiscrepancySequence_round_trip x).symm
      (Eq.trans hread (lowDiscrepancySequence_round_trip y)))

instance lowDiscrepancySequenceBHistCarrier : BHistCarrier LowDiscrepancySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lowDiscrepancySequenceToEventFlow
  fromEventFlow := lowDiscrepancySequenceFromEventFlow

instance lowDiscrepancySequenceChapterTasteGate :
    ChapterTasteGate LowDiscrepancySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lowDiscrepancySequenceFromEventFlow
      (lowDiscrepancySequenceToEventFlow x) = some x
    exact lowDiscrepancySequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (lowDiscrepancySequenceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LowDiscrepancySequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  lowDiscrepancySequenceChapterTasteGate

theorem LowDiscrepancySequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      lowDiscrepancySequenceDecodeBHist
        (lowDiscrepancySequenceEncodeBHist h) = h) ∧
      (∀ x : LowDiscrepancySequenceUp,
        lowDiscrepancySequenceFromEventFlow
          (lowDiscrepancySequenceToEventFlow x) = some x) ∧
        (∀ x y : LowDiscrepancySequenceUp,
          lowDiscrepancySequenceToEventFlow x = lowDiscrepancySequenceToEventFlow y →
            x = y) ∧
          lowDiscrepancySequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact lowDiscrepancySequence_decode_encode_bhist
  · constructor
    · exact lowDiscrepancySequence_round_trip
    · constructor
      · intro x y heq
        exact lowDiscrepancySequenceToEventFlow_injective heq
      · rfl

end BEDC.Derived.LowDiscrepancySequenceUp.TasteGate
