import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

/-!
# LawlikeSequenceUp TasteGate carrier.
-/

namespace BEDC.Derived.LawlikeSequenceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Lawlike sequence packet with the seven rows displayed by the paper carrier. -/
inductive LawlikeSequenceUp : Type where
  | mk : (R W O H C P N : BHist) → LawlikeSequenceUp

def lawlikeSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lawlikeSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lawlikeSequenceEncodeBHist h

def lawlikeSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lawlikeSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lawlikeSequenceDecodeBHist tail)

private theorem lawlikeSequenceDecode_encode_bhist :
    ∀ h : BHist, lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def lawlikeSequenceToEventFlow : LawlikeSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LawlikeSequenceUp.mk R W O H C P N =>
      [[BMark.b0],
        lawlikeSequenceEncodeBHist R,
        [BMark.b1, BMark.b0],
        lawlikeSequenceEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b0],
        lawlikeSequenceEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lawlikeSequenceEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lawlikeSequenceEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lawlikeSequenceEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lawlikeSequenceEncodeBHist N]

def lawlikeSequenceFromEventFlow : EventFlow → Option LawlikeSequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag0 :: R :: _tag1 :: W :: _tag2 :: O :: _tag3 :: H :: _tag4 :: C :: _tag5 ::
      P :: _tag6 :: N :: [] =>
      some (LawlikeSequenceUp.mk
        (lawlikeSequenceDecodeBHist R) (lawlikeSequenceDecodeBHist W)
        (lawlikeSequenceDecodeBHist O) (lawlikeSequenceDecodeBHist H)
        (lawlikeSequenceDecodeBHist C) (lawlikeSequenceDecodeBHist P)
        (lawlikeSequenceDecodeBHist N))
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
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ =>
      none

private theorem lawlikeSequence_round_trip :
    ∀ x : LawlikeSequenceUp,
      lawlikeSequenceFromEventFlow (lawlikeSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R W O H C P N =>
      change
        some
          (LawlikeSequenceUp.mk
            (lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist R))
            (lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist W))
            (lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist O))
            (lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist H))
            (lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist C))
            (lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist P))
            (lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist N))) =
          some (LawlikeSequenceUp.mk R W O H C P N)
      have hR := lawlikeSequenceDecode_encode_bhist R
      have hW := lawlikeSequenceDecode_encode_bhist W
      have hO := lawlikeSequenceDecode_encode_bhist O
      have hH := lawlikeSequenceDecode_encode_bhist H
      have hC := lawlikeSequenceDecode_encode_bhist C
      have hP := lawlikeSequenceDecode_encode_bhist P
      have hN := lawlikeSequenceDecode_encode_bhist N
      rw [hR, hW, hO, hH, hC, hP, hN]

theorem lawlikeSequenceToEventFlow_injective {x y : LawlikeSequenceUp} :
    lawlikeSequenceToEventFlow x = lawlikeSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk R1 W1 O1 H1 C1 P1 N1 =>
      cases y with
      | mk R2 W2 O2 H2 C2 P2 N2 =>
          injection heq with _ htail0
          injection htail0 with hR htail1
          injection htail1 with _ htail2
          injection htail2 with hW htail3
          injection htail3 with _ htail4
          injection htail4 with hO htail5
          injection htail5 with _ htail6
          injection htail6 with hH htail7
          injection htail7 with _ htail8
          injection htail8 with hC htail9
          injection htail9 with _ htail10
          injection htail10 with hP htail11
          injection htail11 with _ htail12
          injection htail12 with hN _
          have hR' : R1 = R2 := by
            have decoded := congrArg lawlikeSequenceDecodeBHist hR
            exact Eq.trans (lawlikeSequenceDecode_encode_bhist R1).symm
              (Eq.trans decoded (lawlikeSequenceDecode_encode_bhist R2))
          cases hR'
          have hW' : W1 = W2 := by
            have decoded := congrArg lawlikeSequenceDecodeBHist hW
            exact Eq.trans (lawlikeSequenceDecode_encode_bhist W1).symm
              (Eq.trans decoded (lawlikeSequenceDecode_encode_bhist W2))
          cases hW'
          have hO' : O1 = O2 := by
            have decoded := congrArg lawlikeSequenceDecodeBHist hO
            exact Eq.trans (lawlikeSequenceDecode_encode_bhist O1).symm
              (Eq.trans decoded (lawlikeSequenceDecode_encode_bhist O2))
          cases hO'
          have hH' : H1 = H2 := by
            have decoded := congrArg lawlikeSequenceDecodeBHist hH
            exact Eq.trans (lawlikeSequenceDecode_encode_bhist H1).symm
              (Eq.trans decoded (lawlikeSequenceDecode_encode_bhist H2))
          cases hH'
          have hC' : C1 = C2 := by
            have decoded := congrArg lawlikeSequenceDecodeBHist hC
            exact Eq.trans (lawlikeSequenceDecode_encode_bhist C1).symm
              (Eq.trans decoded (lawlikeSequenceDecode_encode_bhist C2))
          cases hC'
          have hP' : P1 = P2 := by
            have decoded := congrArg lawlikeSequenceDecodeBHist hP
            exact Eq.trans (lawlikeSequenceDecode_encode_bhist P1).symm
              (Eq.trans decoded (lawlikeSequenceDecode_encode_bhist P2))
          cases hP'
          have hN' : N1 = N2 := by
            have decoded := congrArg lawlikeSequenceDecodeBHist hN
            exact Eq.trans (lawlikeSequenceDecode_encode_bhist N1).symm
              (Eq.trans decoded (lawlikeSequenceDecode_encode_bhist N2))
          cases hN'
          rfl

instance lawlikeSequenceBHistCarrier : BHistCarrier LawlikeSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lawlikeSequenceToEventFlow
  fromEventFlow := lawlikeSequenceFromEventFlow

instance lawlikeSequenceChapterTasteGate : ChapterTasteGate LawlikeSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lawlikeSequenceFromEventFlow (lawlikeSequenceToEventFlow x) = some x
    exact lawlikeSequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (lawlikeSequenceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LawlikeSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  lawlikeSequenceChapterTasteGate

theorem LawlikeSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, lawlikeSequenceDecodeBHist (lawlikeSequenceEncodeBHist h) = h) ∧
      (∀ x : LawlikeSequenceUp,
        lawlikeSequenceFromEventFlow (lawlikeSequenceToEventFlow x) = some x) ∧
      (∀ x y : LawlikeSequenceUp,
        lawlikeSequenceToEventFlow x = lawlikeSequenceToEventFlow y → x = y) ∧
      lawlikeSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact lawlikeSequenceDecode_encode_bhist
  · constructor
    · exact lawlikeSequence_round_trip
    · constructor
      · intro x y heq
        exact lawlikeSequenceToEventFlow_injective heq
      · rfl

end BEDC.Derived.LawlikeSequenceUp.TasteGate
