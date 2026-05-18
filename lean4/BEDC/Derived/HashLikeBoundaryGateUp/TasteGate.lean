import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HashLikeBoundaryGateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HashLikeBoundaryGateUp : Type where
  | mk : (D F E R V H C P N : BHist) → HashLikeBoundaryGateUp
  deriving DecidableEq

def HashLikeBoundaryGateTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: HashLikeBoundaryGateTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: HashLikeBoundaryGateTasteGate_single_carrier_alignment_encodeBHist h

def HashLikeBoundaryGateTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (HashLikeBoundaryGateTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (HashLikeBoundaryGateTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem HashLikeBoundaryGateTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      HashLikeBoundaryGateTasteGate_single_carrier_alignment_decodeBHist
        (HashLikeBoundaryGateTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def HashLikeBoundaryGateTasteGate_single_carrier_alignment_fields :
    HashLikeBoundaryGateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HashLikeBoundaryGateUp.mk D F E R V H C P N => [D, F, E, R, V, H, C, P, N]

def HashLikeBoundaryGateTasteGate_single_carrier_alignment_toEventFlow :
    HashLikeBoundaryGateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (HashLikeBoundaryGateTasteGate_single_carrier_alignment_fields x).map
        HashLikeBoundaryGateTasteGate_single_carrier_alignment_encodeBHist

def HashLikeBoundaryGateTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option HashLikeBoundaryGateUp
  -- BEDC touchpoint anchor: BHist BMark
  | D :: F :: E :: R :: V :: H :: C :: P :: N :: [] =>
      some
        (HashLikeBoundaryGateUp.mk
          (HashLikeBoundaryGateTasteGate_single_carrier_alignment_decodeBHist D)
          (HashLikeBoundaryGateTasteGate_single_carrier_alignment_decodeBHist F)
          (HashLikeBoundaryGateTasteGate_single_carrier_alignment_decodeBHist E)
          (HashLikeBoundaryGateTasteGate_single_carrier_alignment_decodeBHist R)
          (HashLikeBoundaryGateTasteGate_single_carrier_alignment_decodeBHist V)
          (HashLikeBoundaryGateTasteGate_single_carrier_alignment_decodeBHist H)
          (HashLikeBoundaryGateTasteGate_single_carrier_alignment_decodeBHist C)
          (HashLikeBoundaryGateTasteGate_single_carrier_alignment_decodeBHist P)
          (HashLikeBoundaryGateTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem HashLikeBoundaryGateTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HashLikeBoundaryGateUp,
      HashLikeBoundaryGateTasteGate_single_carrier_alignment_fromEventFlow
        (HashLikeBoundaryGateTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D F E R V H C P N =>
      change
        some
          (HashLikeBoundaryGateUp.mk
            (HashLikeBoundaryGateTasteGate_single_carrier_alignment_decodeBHist
              (HashLikeBoundaryGateTasteGate_single_carrier_alignment_encodeBHist D))
            (HashLikeBoundaryGateTasteGate_single_carrier_alignment_decodeBHist
              (HashLikeBoundaryGateTasteGate_single_carrier_alignment_encodeBHist F))
            (HashLikeBoundaryGateTasteGate_single_carrier_alignment_decodeBHist
              (HashLikeBoundaryGateTasteGate_single_carrier_alignment_encodeBHist E))
            (HashLikeBoundaryGateTasteGate_single_carrier_alignment_decodeBHist
              (HashLikeBoundaryGateTasteGate_single_carrier_alignment_encodeBHist R))
            (HashLikeBoundaryGateTasteGate_single_carrier_alignment_decodeBHist
              (HashLikeBoundaryGateTasteGate_single_carrier_alignment_encodeBHist V))
            (HashLikeBoundaryGateTasteGate_single_carrier_alignment_decodeBHist
              (HashLikeBoundaryGateTasteGate_single_carrier_alignment_encodeBHist H))
            (HashLikeBoundaryGateTasteGate_single_carrier_alignment_decodeBHist
              (HashLikeBoundaryGateTasteGate_single_carrier_alignment_encodeBHist C))
            (HashLikeBoundaryGateTasteGate_single_carrier_alignment_decodeBHist
              (HashLikeBoundaryGateTasteGate_single_carrier_alignment_encodeBHist P))
            (HashLikeBoundaryGateTasteGate_single_carrier_alignment_decodeBHist
              (HashLikeBoundaryGateTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (HashLikeBoundaryGateUp.mk D F E R V H C P N)
      rw [HashLikeBoundaryGateTasteGate_single_carrier_alignment_decode_encode D,
        HashLikeBoundaryGateTasteGate_single_carrier_alignment_decode_encode F,
        HashLikeBoundaryGateTasteGate_single_carrier_alignment_decode_encode E,
        HashLikeBoundaryGateTasteGate_single_carrier_alignment_decode_encode R,
        HashLikeBoundaryGateTasteGate_single_carrier_alignment_decode_encode V,
        HashLikeBoundaryGateTasteGate_single_carrier_alignment_decode_encode H,
        HashLikeBoundaryGateTasteGate_single_carrier_alignment_decode_encode C,
        HashLikeBoundaryGateTasteGate_single_carrier_alignment_decode_encode P,
        HashLikeBoundaryGateTasteGate_single_carrier_alignment_decode_encode N]

private theorem HashLikeBoundaryGateTasteGate_single_carrier_alignment_injective
    {x y : HashLikeBoundaryGateUp} :
    HashLikeBoundaryGateTasteGate_single_carrier_alignment_toEventFlow x =
      HashLikeBoundaryGateTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      HashLikeBoundaryGateTasteGate_single_carrier_alignment_fromEventFlow
          (HashLikeBoundaryGateTasteGate_single_carrier_alignment_toEventFlow x) =
        HashLikeBoundaryGateTasteGate_single_carrier_alignment_fromEventFlow
          (HashLikeBoundaryGateTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg HashLikeBoundaryGateTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HashLikeBoundaryGateTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HashLikeBoundaryGateTasteGate_single_carrier_alignment_round_trip y)))

private theorem HashLikeBoundaryGateTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : HashLikeBoundaryGateUp,
      HashLikeBoundaryGateTasteGate_single_carrier_alignment_fields x =
        HashLikeBoundaryGateTasteGate_single_carrier_alignment_fields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk D1 F1 E1 R1 V1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 F2 E2 R2 V2 H2 C2 P2 N2 =>
          injection h with hD t1
          injection t1 with hF t2
          injection t2 with hE t3
          injection t3 with hR t4
          injection t4 with hV t5
          injection t5 with hH t6
          injection t6 with hC t7
          injection t7 with hP t8
          injection t8 with hN _
          subst hD
          subst hF
          subst hE
          subst hR
          subst hV
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance hashLikeBoundaryGateBHistCarrier :
    BHistCarrier HashLikeBoundaryGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := HashLikeBoundaryGateTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := HashLikeBoundaryGateTasteGate_single_carrier_alignment_fromEventFlow

instance hashLikeBoundaryGateChapterTasteGate :
    ChapterTasteGate HashLikeBoundaryGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      HashLikeBoundaryGateTasteGate_single_carrier_alignment_fromEventFlow
          (HashLikeBoundaryGateTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact HashLikeBoundaryGateTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HashLikeBoundaryGateTasteGate_single_carrier_alignment_injective heq)

instance hashLikeBoundaryGateFieldFaithful :
    FieldFaithful HashLikeBoundaryGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := HashLikeBoundaryGateTasteGate_single_carrier_alignment_fields
  field_faithful := HashLikeBoundaryGateTasteGate_single_carrier_alignment_field_faithful

instance hashLikeBoundaryGateNontrivial :
    Nontrivial HashLikeBoundaryGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HashLikeBoundaryGateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HashLikeBoundaryGateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HashLikeBoundaryGateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hashLikeBoundaryGateChapterTasteGate

theorem HashLikeBoundaryGateTasteGate_single_carrier_alignment :
    ∀ D F E R V H C P N : BHist,
      HashLikeBoundaryGateTasteGate_single_carrier_alignment_fields
          (HashLikeBoundaryGateUp.mk D F E R V H C P N) =
        [D, F, E, R, V, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist BMark
  intro D F E R V H C P N
  rfl

end BEDC.Derived.HashLikeBoundaryGateUp
