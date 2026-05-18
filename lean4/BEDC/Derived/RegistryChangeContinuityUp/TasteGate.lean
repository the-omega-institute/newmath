import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegistryChangeContinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegistryChangeContinuityUp : Type where
  | mk : (T A D S R B H C P N : BHist) → RegistryChangeContinuityUp
  deriving DecidableEq

def RegistryChangeContinuityTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: RegistryChangeContinuityTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: RegistryChangeContinuityTasteGate_single_carrier_alignment_encodeBHist h

def RegistryChangeContinuityTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (RegistryChangeContinuityTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (RegistryChangeContinuityTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem RegistryChangeContinuityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      RegistryChangeContinuityTasteGate_single_carrier_alignment_decodeBHist
        (RegistryChangeContinuityTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def RegistryChangeContinuityTasteGate_single_carrier_alignment_fields :
    RegistryChangeContinuityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegistryChangeContinuityUp.mk T A D S R B H C P N => [T, A, D, S, R, B, H, C, P, N]

def RegistryChangeContinuityTasteGate_single_carrier_alignment_toEventFlow :
    RegistryChangeContinuityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (RegistryChangeContinuityTasteGate_single_carrier_alignment_fields x).map
        RegistryChangeContinuityTasteGate_single_carrier_alignment_encodeBHist

def RegistryChangeContinuityTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option RegistryChangeContinuityUp
  -- BEDC touchpoint anchor: BHist BMark
  | T :: A :: D :: S :: R :: B :: H :: C :: P :: N :: [] =>
      some
        (RegistryChangeContinuityUp.mk
          (RegistryChangeContinuityTasteGate_single_carrier_alignment_decodeBHist T)
          (RegistryChangeContinuityTasteGate_single_carrier_alignment_decodeBHist A)
          (RegistryChangeContinuityTasteGate_single_carrier_alignment_decodeBHist D)
          (RegistryChangeContinuityTasteGate_single_carrier_alignment_decodeBHist S)
          (RegistryChangeContinuityTasteGate_single_carrier_alignment_decodeBHist R)
          (RegistryChangeContinuityTasteGate_single_carrier_alignment_decodeBHist B)
          (RegistryChangeContinuityTasteGate_single_carrier_alignment_decodeBHist H)
          (RegistryChangeContinuityTasteGate_single_carrier_alignment_decodeBHist C)
          (RegistryChangeContinuityTasteGate_single_carrier_alignment_decodeBHist P)
          (RegistryChangeContinuityTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem RegistryChangeContinuityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegistryChangeContinuityUp,
      RegistryChangeContinuityTasteGate_single_carrier_alignment_fromEventFlow
        (RegistryChangeContinuityTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T A D S R B H C P N =>
      change
        some
          (RegistryChangeContinuityUp.mk
            (RegistryChangeContinuityTasteGate_single_carrier_alignment_decodeBHist
              (RegistryChangeContinuityTasteGate_single_carrier_alignment_encodeBHist T))
            (RegistryChangeContinuityTasteGate_single_carrier_alignment_decodeBHist
              (RegistryChangeContinuityTasteGate_single_carrier_alignment_encodeBHist A))
            (RegistryChangeContinuityTasteGate_single_carrier_alignment_decodeBHist
              (RegistryChangeContinuityTasteGate_single_carrier_alignment_encodeBHist D))
            (RegistryChangeContinuityTasteGate_single_carrier_alignment_decodeBHist
              (RegistryChangeContinuityTasteGate_single_carrier_alignment_encodeBHist S))
            (RegistryChangeContinuityTasteGate_single_carrier_alignment_decodeBHist
              (RegistryChangeContinuityTasteGate_single_carrier_alignment_encodeBHist R))
            (RegistryChangeContinuityTasteGate_single_carrier_alignment_decodeBHist
              (RegistryChangeContinuityTasteGate_single_carrier_alignment_encodeBHist B))
            (RegistryChangeContinuityTasteGate_single_carrier_alignment_decodeBHist
              (RegistryChangeContinuityTasteGate_single_carrier_alignment_encodeBHist H))
            (RegistryChangeContinuityTasteGate_single_carrier_alignment_decodeBHist
              (RegistryChangeContinuityTasteGate_single_carrier_alignment_encodeBHist C))
            (RegistryChangeContinuityTasteGate_single_carrier_alignment_decodeBHist
              (RegistryChangeContinuityTasteGate_single_carrier_alignment_encodeBHist P))
            (RegistryChangeContinuityTasteGate_single_carrier_alignment_decodeBHist
              (RegistryChangeContinuityTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (RegistryChangeContinuityUp.mk T A D S R B H C P N)
      rw [RegistryChangeContinuityTasteGate_single_carrier_alignment_decode_encode T,
        RegistryChangeContinuityTasteGate_single_carrier_alignment_decode_encode A,
        RegistryChangeContinuityTasteGate_single_carrier_alignment_decode_encode D,
        RegistryChangeContinuityTasteGate_single_carrier_alignment_decode_encode S,
        RegistryChangeContinuityTasteGate_single_carrier_alignment_decode_encode R,
        RegistryChangeContinuityTasteGate_single_carrier_alignment_decode_encode B,
        RegistryChangeContinuityTasteGate_single_carrier_alignment_decode_encode H,
        RegistryChangeContinuityTasteGate_single_carrier_alignment_decode_encode C,
        RegistryChangeContinuityTasteGate_single_carrier_alignment_decode_encode P,
        RegistryChangeContinuityTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegistryChangeContinuityTasteGate_single_carrier_alignment_injective
    {x y : RegistryChangeContinuityUp} :
    RegistryChangeContinuityTasteGate_single_carrier_alignment_toEventFlow x =
      RegistryChangeContinuityTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      RegistryChangeContinuityTasteGate_single_carrier_alignment_fromEventFlow
          (RegistryChangeContinuityTasteGate_single_carrier_alignment_toEventFlow x) =
        RegistryChangeContinuityTasteGate_single_carrier_alignment_fromEventFlow
          (RegistryChangeContinuityTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg RegistryChangeContinuityTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegistryChangeContinuityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegistryChangeContinuityTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegistryChangeContinuityTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : RegistryChangeContinuityUp,
      RegistryChangeContinuityTasteGate_single_carrier_alignment_fields x =
        RegistryChangeContinuityTasteGate_single_carrier_alignment_fields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk T1 A1 D1 S1 R1 B1 H1 C1 P1 N1 =>
      cases y with
      | mk T2 A2 D2 S2 R2 B2 H2 C2 P2 N2 =>
          injection h with hT t1
          injection t1 with hA t2
          injection t2 with hD t3
          injection t3 with hS t4
          injection t4 with hR t5
          injection t5 with hB t6
          injection t6 with hH t7
          injection t7 with hC t8
          injection t8 with hP t9
          injection t9 with hN _
          subst hT
          subst hA
          subst hD
          subst hS
          subst hR
          subst hB
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance registryChangeContinuityBHistCarrier :
    BHistCarrier RegistryChangeContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := RegistryChangeContinuityTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := RegistryChangeContinuityTasteGate_single_carrier_alignment_fromEventFlow

instance registryChangeContinuityChapterTasteGate :
    ChapterTasteGate RegistryChangeContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      RegistryChangeContinuityTasteGate_single_carrier_alignment_fromEventFlow
          (RegistryChangeContinuityTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact RegistryChangeContinuityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegistryChangeContinuityTasteGate_single_carrier_alignment_injective heq)

instance registryChangeContinuityFieldFaithful :
    FieldFaithful RegistryChangeContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := RegistryChangeContinuityTasteGate_single_carrier_alignment_fields
  field_faithful :=
    RegistryChangeContinuityTasteGate_single_carrier_alignment_field_faithful

instance registryChangeContinuityNontrivial :
    Nontrivial RegistryChangeContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegistryChangeContinuityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegistryChangeContinuityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegistryChangeContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  registryChangeContinuityChapterTasteGate

theorem RegistryChangeContinuityTasteGate_single_carrier_alignment :
    ∀ T A D S R B H C P N : BHist,
      RegistryChangeContinuityTasteGate_single_carrier_alignment_fields
          (RegistryChangeContinuityUp.mk T A D S R B H C P N) =
        [T, A, D, S, R, B, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist BMark
  intro T A D S R B H C P N
  rfl

end BEDC.Derived.RegistryChangeContinuityUp
