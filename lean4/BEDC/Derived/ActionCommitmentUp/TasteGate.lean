import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ActionCommitmentUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ActionCommitmentUp : Type where
  | mk : (I R L G T C H Q P N : BHist) → ActionCommitmentUp
  deriving DecidableEq

def ActionCommitmentTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: ActionCommitmentTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: ActionCommitmentTasteGate_single_carrier_alignment_encodeBHist h

def ActionCommitmentTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (ActionCommitmentTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (ActionCommitmentTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem ActionCommitmentTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      ActionCommitmentTasteGate_single_carrier_alignment_decodeBHist
        (ActionCommitmentTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def ActionCommitmentTasteGate_single_carrier_alignment_fields :
    ActionCommitmentUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ActionCommitmentUp.mk I R L G T C H Q P N => [I, R, L, G, T, C, H, Q, P, N]

def ActionCommitmentTasteGate_single_carrier_alignment_toEventFlow :
    ActionCommitmentUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (ActionCommitmentTasteGate_single_carrier_alignment_fields x).map
        ActionCommitmentTasteGate_single_carrier_alignment_encodeBHist

def ActionCommitmentTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option ActionCommitmentUp
  -- BEDC touchpoint anchor: BHist BMark
  | I :: R :: L :: G :: T :: C :: H :: Q :: P :: N :: [] =>
      some
        (ActionCommitmentUp.mk
          (ActionCommitmentTasteGate_single_carrier_alignment_decodeBHist I)
          (ActionCommitmentTasteGate_single_carrier_alignment_decodeBHist R)
          (ActionCommitmentTasteGate_single_carrier_alignment_decodeBHist L)
          (ActionCommitmentTasteGate_single_carrier_alignment_decodeBHist G)
          (ActionCommitmentTasteGate_single_carrier_alignment_decodeBHist T)
          (ActionCommitmentTasteGate_single_carrier_alignment_decodeBHist C)
          (ActionCommitmentTasteGate_single_carrier_alignment_decodeBHist H)
          (ActionCommitmentTasteGate_single_carrier_alignment_decodeBHist Q)
          (ActionCommitmentTasteGate_single_carrier_alignment_decodeBHist P)
          (ActionCommitmentTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem ActionCommitmentTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ActionCommitmentUp,
      ActionCommitmentTasteGate_single_carrier_alignment_fromEventFlow
        (ActionCommitmentTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I R L G T C H Q P N =>
      change
        some
          (ActionCommitmentUp.mk
            (ActionCommitmentTasteGate_single_carrier_alignment_decodeBHist
              (ActionCommitmentTasteGate_single_carrier_alignment_encodeBHist I))
            (ActionCommitmentTasteGate_single_carrier_alignment_decodeBHist
              (ActionCommitmentTasteGate_single_carrier_alignment_encodeBHist R))
            (ActionCommitmentTasteGate_single_carrier_alignment_decodeBHist
              (ActionCommitmentTasteGate_single_carrier_alignment_encodeBHist L))
            (ActionCommitmentTasteGate_single_carrier_alignment_decodeBHist
              (ActionCommitmentTasteGate_single_carrier_alignment_encodeBHist G))
            (ActionCommitmentTasteGate_single_carrier_alignment_decodeBHist
              (ActionCommitmentTasteGate_single_carrier_alignment_encodeBHist T))
            (ActionCommitmentTasteGate_single_carrier_alignment_decodeBHist
              (ActionCommitmentTasteGate_single_carrier_alignment_encodeBHist C))
            (ActionCommitmentTasteGate_single_carrier_alignment_decodeBHist
              (ActionCommitmentTasteGate_single_carrier_alignment_encodeBHist H))
            (ActionCommitmentTasteGate_single_carrier_alignment_decodeBHist
              (ActionCommitmentTasteGate_single_carrier_alignment_encodeBHist Q))
            (ActionCommitmentTasteGate_single_carrier_alignment_decodeBHist
              (ActionCommitmentTasteGate_single_carrier_alignment_encodeBHist P))
            (ActionCommitmentTasteGate_single_carrier_alignment_decodeBHist
              (ActionCommitmentTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (ActionCommitmentUp.mk I R L G T C H Q P N)
      rw [ActionCommitmentTasteGate_single_carrier_alignment_decode_encode I,
        ActionCommitmentTasteGate_single_carrier_alignment_decode_encode R,
        ActionCommitmentTasteGate_single_carrier_alignment_decode_encode L,
        ActionCommitmentTasteGate_single_carrier_alignment_decode_encode G,
        ActionCommitmentTasteGate_single_carrier_alignment_decode_encode T,
        ActionCommitmentTasteGate_single_carrier_alignment_decode_encode C,
        ActionCommitmentTasteGate_single_carrier_alignment_decode_encode H,
        ActionCommitmentTasteGate_single_carrier_alignment_decode_encode Q,
        ActionCommitmentTasteGate_single_carrier_alignment_decode_encode P,
        ActionCommitmentTasteGate_single_carrier_alignment_decode_encode N]

private theorem ActionCommitmentTasteGate_single_carrier_alignment_injective
    {x y : ActionCommitmentUp} :
    ActionCommitmentTasteGate_single_carrier_alignment_toEventFlow x =
      ActionCommitmentTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ActionCommitmentTasteGate_single_carrier_alignment_fromEventFlow
          (ActionCommitmentTasteGate_single_carrier_alignment_toEventFlow x) =
        ActionCommitmentTasteGate_single_carrier_alignment_fromEventFlow
          (ActionCommitmentTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg ActionCommitmentTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ActionCommitmentTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ActionCommitmentTasteGate_single_carrier_alignment_round_trip y)))

private theorem ActionCommitmentTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : ActionCommitmentUp,
      ActionCommitmentTasteGate_single_carrier_alignment_fields x =
        ActionCommitmentTasteGate_single_carrier_alignment_fields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk I1 R1 L1 G1 T1 C1 H1 Q1 P1 N1 =>
      cases y with
      | mk I2 R2 L2 G2 T2 C2 H2 Q2 P2 N2 =>
          injection h with hI t1
          injection t1 with hR t2
          injection t2 with hL t3
          injection t3 with hG t4
          injection t4 with hT t5
          injection t5 with hC t6
          injection t6 with hH t7
          injection t7 with hQ t8
          injection t8 with hP t9
          injection t9 with hN _
          subst hI
          subst hR
          subst hL
          subst hG
          subst hT
          subst hC
          subst hH
          subst hQ
          subst hP
          subst hN
          rfl

instance actionCommitmentBHistCarrier :
    BHistCarrier ActionCommitmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ActionCommitmentTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := ActionCommitmentTasteGate_single_carrier_alignment_fromEventFlow

instance actionCommitmentChapterTasteGate :
    ChapterTasteGate ActionCommitmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      ActionCommitmentTasteGate_single_carrier_alignment_fromEventFlow
          (ActionCommitmentTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact ActionCommitmentTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ActionCommitmentTasteGate_single_carrier_alignment_injective heq)

instance actionCommitmentFieldFaithful :
    FieldFaithful ActionCommitmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := ActionCommitmentTasteGate_single_carrier_alignment_fields
  field_faithful := ActionCommitmentTasteGate_single_carrier_alignment_field_faithful

instance actionCommitmentNontrivial :
    Nontrivial ActionCommitmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ActionCommitmentUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ActionCommitmentUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ActionCommitmentUp :=
  -- BEDC touchpoint anchor: BHist BMark
  actionCommitmentChapterTasteGate

theorem ActionCommitmentTasteGate_single_carrier_alignment :
    ∀ I R L G T C H Q P N : BHist,
      ActionCommitmentTasteGate_single_carrier_alignment_fields
          (ActionCommitmentUp.mk I R L G T C H Q P N) =
        [I, R, L, G, T, C, H, Q, P, N] := by
  -- BEDC touchpoint anchor: BHist BMark
  intro I R L G T C H Q P N
  rfl

end BEDC.Derived.ActionCommitmentUp
