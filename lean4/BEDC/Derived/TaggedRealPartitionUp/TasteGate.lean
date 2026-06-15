import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TaggedRealPartitionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TaggedRealPartitionUp : Type where
  | mk (I M A G O S R E H C P N : BHist) : TaggedRealPartitionUp
  deriving DecidableEq

def taggedRealPartitionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: taggedRealPartitionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: taggedRealPartitionEncodeBHist h

def taggedRealPartitionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (taggedRealPartitionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (taggedRealPartitionDecodeBHist tail)

private theorem TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def TaggedRealPartitionTasteGate_single_carrier_alignment_fields :
    TaggedRealPartitionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TaggedRealPartitionUp.mk I M A G O S R E H C P N =>
      [I, M, A, G, O, S, R, E, H, C, P, N]

def taggedRealPartitionToEventFlow : TaggedRealPartitionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (TaggedRealPartitionTasteGate_single_carrier_alignment_fields x).map
        taggedRealPartitionEncodeBHist

def taggedRealPartitionFromEventFlow : EventFlow → Option TaggedRealPartitionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | I :: rest0 =>
      match rest0 with
      | [] => none
      | M :: rest1 =>
          match rest1 with
          | [] => none
          | A :: rest2 =>
              match rest2 with
              | [] => none
              | G :: rest3 =>
                  match rest3 with
                  | [] => none
                  | O :: rest4 =>
                      match rest4 with
                      | [] => none
                      | S :: rest5 =>
                          match rest5 with
                          | [] => none
                          | R :: rest6 =>
                              match rest6 with
                              | [] => none
                              | E :: rest7 =>
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
                                                        (TaggedRealPartitionUp.mk
                                                          (taggedRealPartitionDecodeBHist I)
                                                          (taggedRealPartitionDecodeBHist M)
                                                          (taggedRealPartitionDecodeBHist A)
                                                          (taggedRealPartitionDecodeBHist G)
                                                          (taggedRealPartitionDecodeBHist O)
                                                          (taggedRealPartitionDecodeBHist S)
                                                          (taggedRealPartitionDecodeBHist R)
                                                          (taggedRealPartitionDecodeBHist E)
                                                          (taggedRealPartitionDecodeBHist H)
                                                          (taggedRealPartitionDecodeBHist C)
                                                          (taggedRealPartitionDecodeBHist P)
                                                          (taggedRealPartitionDecodeBHist N))
                                                  | _ :: _ => none

private theorem TaggedRealPartitionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : TaggedRealPartitionUp,
      taggedRealPartitionFromEventFlow (taggedRealPartitionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I M A G O S R E H C P N =>
      change
        some
          (TaggedRealPartitionUp.mk
            (taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist I))
            (taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist M))
            (taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist A))
            (taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist G))
            (taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist O))
            (taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist S))
            (taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist R))
            (taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist E))
            (taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist H))
            (taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist C))
            (taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist P))
            (taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist N))) =
          some (TaggedRealPartitionUp.mk I M A G O S R E H C P N)
      rw [TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode I,
        TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode M,
        TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode A,
        TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode G,
        TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode O,
        TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode S,
        TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode R,
        TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode E,
        TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode H,
        TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode C,
        TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode P,
        TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode N]

theorem TaggedRealPartitionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : TaggedRealPartitionUp} :
    taggedRealPartitionToEventFlow x = taggedRealPartitionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk I1 M1 A1 G1 O1 S1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 M2 A2 G2 O2 S2 R2 E2 H2 C2 P2 N2 =>
          change
            [taggedRealPartitionEncodeBHist I1, taggedRealPartitionEncodeBHist M1,
              taggedRealPartitionEncodeBHist A1, taggedRealPartitionEncodeBHist G1,
              taggedRealPartitionEncodeBHist O1, taggedRealPartitionEncodeBHist S1,
              taggedRealPartitionEncodeBHist R1, taggedRealPartitionEncodeBHist E1,
              taggedRealPartitionEncodeBHist H1, taggedRealPartitionEncodeBHist C1,
              taggedRealPartitionEncodeBHist P1, taggedRealPartitionEncodeBHist N1] =
              [taggedRealPartitionEncodeBHist I2, taggedRealPartitionEncodeBHist M2,
                taggedRealPartitionEncodeBHist A2, taggedRealPartitionEncodeBHist G2,
                taggedRealPartitionEncodeBHist O2, taggedRealPartitionEncodeBHist S2,
                taggedRealPartitionEncodeBHist R2, taggedRealPartitionEncodeBHist E2,
                taggedRealPartitionEncodeBHist H2, taggedRealPartitionEncodeBHist C2,
                taggedRealPartitionEncodeBHist P2, taggedRealPartitionEncodeBHist N2] at heq
          injection heq with hI t1
          injection t1 with hM t2
          injection t2 with hA t3
          injection t3 with hG t4
          injection t4 with hO t5
          injection t5 with hS t6
          injection t6 with hR t7
          injection t7 with hE t8
          injection t8 with hH t9
          injection t9 with hC t10
          injection t10 with hP t11
          injection t11 with hN _
          have eI : I1 = I2 := by
            have h := congrArg taggedRealPartitionDecodeBHist hI
            rw [TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode I1,
              TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode I2] at h
            exact h
          have eM : M1 = M2 := by
            have h := congrArg taggedRealPartitionDecodeBHist hM
            rw [TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode M1,
              TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode M2] at h
            exact h
          have eA : A1 = A2 := by
            have h := congrArg taggedRealPartitionDecodeBHist hA
            rw [TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode A1,
              TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode A2] at h
            exact h
          have eG : G1 = G2 := by
            have h := congrArg taggedRealPartitionDecodeBHist hG
            rw [TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode G1,
              TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode G2] at h
            exact h
          have eO : O1 = O2 := by
            have h := congrArg taggedRealPartitionDecodeBHist hO
            rw [TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode O1,
              TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode O2] at h
            exact h
          have eS : S1 = S2 := by
            have h := congrArg taggedRealPartitionDecodeBHist hS
            rw [TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode S1,
              TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode S2] at h
            exact h
          have eR : R1 = R2 := by
            have h := congrArg taggedRealPartitionDecodeBHist hR
            rw [TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode R1,
              TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode R2] at h
            exact h
          have eE : E1 = E2 := by
            have h := congrArg taggedRealPartitionDecodeBHist hE
            rw [TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode E1,
              TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode E2] at h
            exact h
          have eH : H1 = H2 := by
            have h := congrArg taggedRealPartitionDecodeBHist hH
            rw [TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode H1,
              TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode H2] at h
            exact h
          have eC : C1 = C2 := by
            have h := congrArg taggedRealPartitionDecodeBHist hC
            rw [TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode C1,
              TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode C2] at h
            exact h
          have eP : P1 = P2 := by
            have h := congrArg taggedRealPartitionDecodeBHist hP
            rw [TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode P1,
              TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode P2] at h
            exact h
          have eN : N1 = N2 := by
            have h := congrArg taggedRealPartitionDecodeBHist hN
            rw [TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode N1,
              TaggedRealPartitionTasteGate_single_carrier_alignment_decode_encode N2] at h
            exact h
          subst eI
          subst eM
          subst eA
          subst eG
          subst eO
          subst eS
          subst eR
          subst eE
          subst eH
          subst eC
          subst eP
          subst eN
          rfl

private theorem TaggedRealPartitionTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : TaggedRealPartitionUp,
      TaggedRealPartitionTasteGate_single_carrier_alignment_fields x =
        TaggedRealPartitionTasteGate_single_carrier_alignment_fields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 M1 A1 G1 O1 S1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 M2 A2 G2 O2 S2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance taggedRealPartitionBHistCarrier : BHistCarrier TaggedRealPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := taggedRealPartitionToEventFlow
  fromEventFlow := taggedRealPartitionFromEventFlow

instance taggedRealPartitionChapterTasteGate : ChapterTasteGate TaggedRealPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change taggedRealPartitionFromEventFlow (taggedRealPartitionToEventFlow x) = some x
    exact TaggedRealPartitionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TaggedRealPartitionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance taggedRealPartitionFieldFaithful : FieldFaithful TaggedRealPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := TaggedRealPartitionTasteGate_single_carrier_alignment_fields
  field_faithful := TaggedRealPartitionTasteGate_single_carrier_alignment_fields_faithful

instance taggedRealPartitionNontrivial : Nontrivial TaggedRealPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TaggedRealPartitionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TaggedRealPartitionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem TaggedRealPartitionTasteGate_single_carrier_alignment :
    (∀ h : BHist, taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist h) = h) ∧
      (∀ x : TaggedRealPartitionUp,
        taggedRealPartitionFromEventFlow (taggedRealPartitionToEventFlow x) = some x) ∧
      (∀ x y : TaggedRealPartitionUp,
        taggedRealPartitionToEventFlow x = taggedRealPartitionToEventFlow y → x = y) ∧
      taggedRealPartitionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  · constructor
    · intro token
      cases token with
      | mk I M A G O S R E H C P N =>
          change
            some
              (TaggedRealPartitionUp.mk
                (taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist I))
                (taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist M))
                (taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist A))
                (taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist G))
                (taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist O))
                (taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist S))
                (taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist R))
                (taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist E))
                (taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist H))
                (taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist C))
                (taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist P))
                (taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist N))) =
              some (TaggedRealPartitionUp.mk I M A G O S R E H C P N)
          have eI : taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist I) = I := by
            induction I with
            | Empty => rfl
            | e0 I ih => exact congrArg BHist.e0 ih
            | e1 I ih => exact congrArg BHist.e1 ih
          have eM : taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist M) = M := by
            induction M with
            | Empty => rfl
            | e0 M ih => exact congrArg BHist.e0 ih
            | e1 M ih => exact congrArg BHist.e1 ih
          have eA : taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist A) = A := by
            induction A with
            | Empty => rfl
            | e0 A ih => exact congrArg BHist.e0 ih
            | e1 A ih => exact congrArg BHist.e1 ih
          have eG : taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist G) = G := by
            induction G with
            | Empty => rfl
            | e0 G ih => exact congrArg BHist.e0 ih
            | e1 G ih => exact congrArg BHist.e1 ih
          have eO : taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist O) = O := by
            induction O with
            | Empty => rfl
            | e0 O ih => exact congrArg BHist.e0 ih
            | e1 O ih => exact congrArg BHist.e1 ih
          have eS : taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist S) = S := by
            induction S with
            | Empty => rfl
            | e0 S ih => exact congrArg BHist.e0 ih
            | e1 S ih => exact congrArg BHist.e1 ih
          have eR : taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist R) = R := by
            induction R with
            | Empty => rfl
            | e0 R ih => exact congrArg BHist.e0 ih
            | e1 R ih => exact congrArg BHist.e1 ih
          have eE : taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist E) = E := by
            induction E with
            | Empty => rfl
            | e0 E ih => exact congrArg BHist.e0 ih
            | e1 E ih => exact congrArg BHist.e1 ih
          have eH : taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist H) = H := by
            induction H with
            | Empty => rfl
            | e0 H ih => exact congrArg BHist.e0 ih
            | e1 H ih => exact congrArg BHist.e1 ih
          have eC : taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist C) = C := by
            induction C with
            | Empty => rfl
            | e0 C ih => exact congrArg BHist.e0 ih
            | e1 C ih => exact congrArg BHist.e1 ih
          have eP : taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist P) = P := by
            induction P with
            | Empty => rfl
            | e0 P ih => exact congrArg BHist.e0 ih
            | e1 P ih => exact congrArg BHist.e1 ih
          have eN : taggedRealPartitionDecodeBHist (taggedRealPartitionEncodeBHist N) = N := by
            induction N with
            | Empty => rfl
            | e0 N ih => exact congrArg BHist.e0 ih
            | e1 N ih => exact congrArg BHist.e1 ih
          rw [eI, eM, eA, eG, eO, eS, eR, eE, eH, eC, eP, eN]
    · constructor
      · intro x y heq
        exact TaggedRealPartitionTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.TaggedRealPartitionUp
