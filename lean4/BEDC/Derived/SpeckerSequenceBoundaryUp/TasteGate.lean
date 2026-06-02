import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SpeckerSequenceBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SpeckerSequenceBoundaryUp : Type where
  | mk (S W D M R L H C P N : BHist) : SpeckerSequenceBoundaryUp
  deriving DecidableEq

def speckerSequenceBoundaryEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: speckerSequenceBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: speckerSequenceBoundaryEncodeBHist h

def speckerSequenceBoundaryDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (speckerSequenceBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (speckerSequenceBoundaryDecodeBHist tail)

private theorem SpeckerSequenceBoundaryTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      speckerSequenceBoundaryDecodeBHist
        (speckerSequenceBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def speckerSequenceBoundaryFields : SpeckerSequenceBoundaryUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SpeckerSequenceBoundaryUp.mk S W D M R L H C P N =>
      [S, W, D, M, R, L, H, C, P, N]

def speckerSequenceBoundaryToEventFlow :
    SpeckerSequenceBoundaryUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (speckerSequenceBoundaryFields x).map speckerSequenceBoundaryEncodeBHist

def speckerSequenceBoundaryFromEventFlow :
    EventFlow -> Option SpeckerSequenceBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | M :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | L :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (SpeckerSequenceBoundaryUp.mk
                                                  (speckerSequenceBoundaryDecodeBHist S)
                                                  (speckerSequenceBoundaryDecodeBHist W)
                                                  (speckerSequenceBoundaryDecodeBHist D)
                                                  (speckerSequenceBoundaryDecodeBHist M)
                                                  (speckerSequenceBoundaryDecodeBHist R)
                                                  (speckerSequenceBoundaryDecodeBHist L)
                                                  (speckerSequenceBoundaryDecodeBHist H)
                                                  (speckerSequenceBoundaryDecodeBHist C)
                                                  (speckerSequenceBoundaryDecodeBHist P)
                                                  (speckerSequenceBoundaryDecodeBHist N))
                                          | _ :: _ => none

private theorem SpeckerSequenceBoundaryTasteGate_single_carrier_alignment_round_trip :
    forall x : SpeckerSequenceBoundaryUp,
      speckerSequenceBoundaryFromEventFlow
          (speckerSequenceBoundaryToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S W D M R L H C P N =>
      change
        some
          (SpeckerSequenceBoundaryUp.mk
            (speckerSequenceBoundaryDecodeBHist
              (speckerSequenceBoundaryEncodeBHist S))
            (speckerSequenceBoundaryDecodeBHist
              (speckerSequenceBoundaryEncodeBHist W))
            (speckerSequenceBoundaryDecodeBHist
              (speckerSequenceBoundaryEncodeBHist D))
            (speckerSequenceBoundaryDecodeBHist
              (speckerSequenceBoundaryEncodeBHist M))
            (speckerSequenceBoundaryDecodeBHist
              (speckerSequenceBoundaryEncodeBHist R))
            (speckerSequenceBoundaryDecodeBHist
              (speckerSequenceBoundaryEncodeBHist L))
            (speckerSequenceBoundaryDecodeBHist
              (speckerSequenceBoundaryEncodeBHist H))
            (speckerSequenceBoundaryDecodeBHist
              (speckerSequenceBoundaryEncodeBHist C))
            (speckerSequenceBoundaryDecodeBHist
              (speckerSequenceBoundaryEncodeBHist P))
            (speckerSequenceBoundaryDecodeBHist
              (speckerSequenceBoundaryEncodeBHist N))) =
          some (SpeckerSequenceBoundaryUp.mk S W D M R L H C P N)
      rw [SpeckerSequenceBoundaryTasteGate_single_carrier_alignment_decode_encode S,
        SpeckerSequenceBoundaryTasteGate_single_carrier_alignment_decode_encode W,
        SpeckerSequenceBoundaryTasteGate_single_carrier_alignment_decode_encode D,
        SpeckerSequenceBoundaryTasteGate_single_carrier_alignment_decode_encode M,
        SpeckerSequenceBoundaryTasteGate_single_carrier_alignment_decode_encode R,
        SpeckerSequenceBoundaryTasteGate_single_carrier_alignment_decode_encode L,
        SpeckerSequenceBoundaryTasteGate_single_carrier_alignment_decode_encode H,
        SpeckerSequenceBoundaryTasteGate_single_carrier_alignment_decode_encode C,
        SpeckerSequenceBoundaryTasteGate_single_carrier_alignment_decode_encode P,
        SpeckerSequenceBoundaryTasteGate_single_carrier_alignment_decode_encode N]

private theorem SpeckerSequenceBoundaryTasteGate_single_carrier_alignment_injective
    {x y : SpeckerSequenceBoundaryUp} :
    speckerSequenceBoundaryToEventFlow x =
      speckerSequenceBoundaryToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      speckerSequenceBoundaryFromEventFlow
          (speckerSequenceBoundaryToEventFlow x) =
        speckerSequenceBoundaryFromEventFlow
          (speckerSequenceBoundaryToEventFlow y) :=
    congrArg speckerSequenceBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SpeckerSequenceBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SpeckerSequenceBoundaryTasteGate_single_carrier_alignment_round_trip y)))

private theorem SpeckerSequenceBoundaryTasteGate_single_carrier_alignment_field_faithful :
    forall x y : SpeckerSequenceBoundaryUp,
      speckerSequenceBoundaryFields x = speckerSequenceBoundaryFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk S1 W1 D1 M1 R1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 W2 D2 M2 R2 L2 H2 C2 P2 N2 =>
          injection h with hS t1
          injection t1 with hW t2
          injection t2 with hD t3
          injection t3 with hM t4
          injection t4 with hR t5
          injection t5 with hL t6
          injection t6 with hH t7
          injection t7 with hC t8
          injection t8 with hP t9
          injection t9 with hN _
          subst hS
          subst hW
          subst hD
          subst hM
          subst hR
          subst hL
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance speckerSequenceBoundaryBHistCarrier :
    BHistCarrier SpeckerSequenceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := speckerSequenceBoundaryToEventFlow
  fromEventFlow := speckerSequenceBoundaryFromEventFlow

instance speckerSequenceBoundaryChapterTasteGate :
    ChapterTasteGate SpeckerSequenceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      speckerSequenceBoundaryFromEventFlow
          (speckerSequenceBoundaryToEventFlow x) =
        some x
    exact SpeckerSequenceBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SpeckerSequenceBoundaryTasteGate_single_carrier_alignment_injective heq)

instance speckerSequenceBoundaryFieldFaithful :
    FieldFaithful SpeckerSequenceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := speckerSequenceBoundaryFields
  field_faithful := SpeckerSequenceBoundaryTasteGate_single_carrier_alignment_field_faithful

instance speckerSequenceBoundaryNontrivial : Nontrivial SpeckerSequenceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SpeckerSequenceBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SpeckerSequenceBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SpeckerSequenceBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  speckerSequenceBoundaryChapterTasteGate

theorem SpeckerSequenceBoundaryTasteGate_single_carrier_alignment :
    (forall h : BHist,
      speckerSequenceBoundaryDecodeBHist
        (speckerSequenceBoundaryEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SpeckerSequenceBoundaryUp) ∧
        Nonempty (ChapterTasteGate SpeckerSequenceBoundaryUp) ∧
          speckerSequenceBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact SpeckerSequenceBoundaryTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact ⟨speckerSequenceBoundaryBHistCarrier⟩
    · constructor
      · exact ⟨speckerSequenceBoundaryChapterTasteGate⟩
      · rfl

end BEDC.Derived.SpeckerSequenceBoundaryUp
