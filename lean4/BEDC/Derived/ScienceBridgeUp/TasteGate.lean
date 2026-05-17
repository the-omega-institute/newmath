import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ScienceBridgeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ScienceBridgeUp : Type where
  | mk : (R O A T B G F H C P N : BHist) → ScienceBridgeUp
  deriving DecidableEq

def scienceBridgeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: scienceBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: scienceBridgeEncodeBHist h

def scienceBridgeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (scienceBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (scienceBridgeDecodeBHist tail)

theorem ScienceBridgeTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, scienceBridgeDecodeBHist (scienceBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def scienceBridgeToEventFlow : ScienceBridgeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ScienceBridgeUp.mk R O A T B G F H C P N =>
      [[BMark.b0],
        scienceBridgeEncodeBHist R,
        [BMark.b1, BMark.b0],
        scienceBridgeEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b0],
        scienceBridgeEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        scienceBridgeEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        scienceBridgeEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        scienceBridgeEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        scienceBridgeEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        scienceBridgeEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        scienceBridgeEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        scienceBridgeEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        scienceBridgeEncodeBHist N]

def scienceBridgeFromEventFlow : EventFlow → Option ScienceBridgeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | R :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | O :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | A :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | T :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | B :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | G :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | F :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | H :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | C :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | P :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | N :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (ScienceBridgeUp.mk
                                                                                                  (scienceBridgeDecodeBHist R)
                                                                                                  (scienceBridgeDecodeBHist O)
                                                                                                  (scienceBridgeDecodeBHist A)
                                                                                                  (scienceBridgeDecodeBHist T)
                                                                                                  (scienceBridgeDecodeBHist B)
                                                                                                  (scienceBridgeDecodeBHist G)
                                                                                                  (scienceBridgeDecodeBHist F)
                                                                                                  (scienceBridgeDecodeBHist H)
                                                                                                  (scienceBridgeDecodeBHist C)
                                                                                                  (scienceBridgeDecodeBHist P)
                                                                                                  (scienceBridgeDecodeBHist N))
                                                                                          | _ :: _ => none

theorem ScienceBridgeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ScienceBridgeUp,
      scienceBridgeFromEventFlow (scienceBridgeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R O A T B G F H C P N =>
      change
        some
          (ScienceBridgeUp.mk
            (scienceBridgeDecodeBHist (scienceBridgeEncodeBHist R))
            (scienceBridgeDecodeBHist (scienceBridgeEncodeBHist O))
            (scienceBridgeDecodeBHist (scienceBridgeEncodeBHist A))
            (scienceBridgeDecodeBHist (scienceBridgeEncodeBHist T))
            (scienceBridgeDecodeBHist (scienceBridgeEncodeBHist B))
            (scienceBridgeDecodeBHist (scienceBridgeEncodeBHist G))
            (scienceBridgeDecodeBHist (scienceBridgeEncodeBHist F))
            (scienceBridgeDecodeBHist (scienceBridgeEncodeBHist H))
            (scienceBridgeDecodeBHist (scienceBridgeEncodeBHist C))
            (scienceBridgeDecodeBHist (scienceBridgeEncodeBHist P))
            (scienceBridgeDecodeBHist (scienceBridgeEncodeBHist N))) =
          some (ScienceBridgeUp.mk R O A T B G F H C P N)
      rw [ScienceBridgeTasteGate_single_carrier_alignment_decode R,
        ScienceBridgeTasteGate_single_carrier_alignment_decode O,
        ScienceBridgeTasteGate_single_carrier_alignment_decode A,
        ScienceBridgeTasteGate_single_carrier_alignment_decode T,
        ScienceBridgeTasteGate_single_carrier_alignment_decode B,
        ScienceBridgeTasteGate_single_carrier_alignment_decode G,
        ScienceBridgeTasteGate_single_carrier_alignment_decode F,
        ScienceBridgeTasteGate_single_carrier_alignment_decode H,
        ScienceBridgeTasteGate_single_carrier_alignment_decode C,
        ScienceBridgeTasteGate_single_carrier_alignment_decode P,
        ScienceBridgeTasteGate_single_carrier_alignment_decode N]

theorem ScienceBridgeTasteGate_single_carrier_alignment_injective
    {x y : ScienceBridgeUp} :
    scienceBridgeToEventFlow x = scienceBridgeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      scienceBridgeFromEventFlow (scienceBridgeToEventFlow x) =
        scienceBridgeFromEventFlow (scienceBridgeToEventFlow y) :=
    congrArg scienceBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ScienceBridgeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ScienceBridgeTasteGate_single_carrier_alignment_round_trip y)))

instance scienceBridgeBHistCarrier : BHistCarrier ScienceBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := scienceBridgeToEventFlow
  fromEventFlow := scienceBridgeFromEventFlow

instance scienceBridgeChapterTasteGate : ChapterTasteGate ScienceBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change scienceBridgeFromEventFlow (scienceBridgeToEventFlow x) = some x
    exact ScienceBridgeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ScienceBridgeTasteGate_single_carrier_alignment_injective heq)

instance scienceBridgeFieldFaithful : FieldFaithful ScienceBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ScienceBridgeUp.mk R O A T B G F H C P N => [R, O, A, T, B, G, F, H, C, P, N]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk R1 O1 A1 T1 B1 G1 F1 H1 C1 P1 N1 =>
        cases y with
        | mk R2 O2 A2 T2 B2 G2 F2 H2 C2 P2 N2 =>
            injection hfields with hR tail1
            cases hR
            injection tail1 with hO tail2
            cases hO
            injection tail2 with hA tail3
            cases hA
            injection tail3 with hT tail4
            cases hT
            injection tail4 with hB tail5
            cases hB
            injection tail5 with hG tail6
            cases hG
            injection tail6 with hF tail7
            cases hF
            injection tail7 with hH tail8
            cases hH
            injection tail8 with hC tail9
            cases hC
            injection tail9 with hP tail10
            cases hP
            injection tail10 with hN _
            cases hN
            rfl

instance scienceBridgeNontrivial : Nontrivial ScienceBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ScienceBridgeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ScienceBridgeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        injection h with hR
        cases hR⟩

def taste_gate : ChapterTasteGate ScienceBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  scienceBridgeChapterTasteGate

theorem ScienceBridgeTasteGate_single_carrier_alignment :
    (∀ h : BHist, scienceBridgeDecodeBHist (scienceBridgeEncodeBHist h) = h) ∧
      (∀ x : ScienceBridgeUp,
        scienceBridgeFromEventFlow (scienceBridgeToEventFlow x) = some x) ∧
        (∀ x y : ScienceBridgeUp,
          scienceBridgeToEventFlow x = scienceBridgeToEventFlow y → x = y) ∧
          scienceBridgeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ScienceBridgeTasteGate_single_carrier_alignment_decode
  · constructor
    · exact ScienceBridgeTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact ScienceBridgeTasteGate_single_carrier_alignment_injective heq
      · rfl

namespace TasteGate

theorem ScienceBridgeTasteGate_single_carrier_alignment :
    scienceBridgeToEventFlow
      (ScienceBridgeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [[BMark.b0], [], [BMark.b1, BMark.b0], [],
          [BMark.b1, BMark.b1, BMark.b0], [],
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0], [],
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0], [],
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0], [],
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          [],
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          [],
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          [],
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b0],
          [],
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          []] ∧
      Nonempty (ChapterTasteGate ScienceBridgeUp) ∧ Nonempty (FieldFaithful ScienceBridgeUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · exact Nonempty.intro scienceBridgeChapterTasteGate
    · exact Nonempty.intro scienceBridgeFieldFaithful

end TasteGate

end BEDC.Derived.ScienceBridgeUp
