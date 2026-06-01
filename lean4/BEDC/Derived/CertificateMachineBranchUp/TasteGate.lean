import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CertificateMachineBranchUp.TasteGate

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CertificateMachineBranchUp : Type where
  | branch (K A D L G R S H C P N : BHist) : CertificateMachineBranchUp
  deriving DecidableEq

def CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist h

def CertificateMachineBranchTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (CertificateMachineBranchTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (CertificateMachineBranchTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CertificateMachineBranchTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CertificateMachineBranchTasteGate_single_carrier_alignment_decodeBHist
          (CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CertificateMachineBranchTasteGate_single_carrier_alignment_fields :
    CertificateMachineBranchUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CertificateMachineBranchUp.branch K A D L G R S H C P N =>
      [K, A, D, L, G, R, S, H, C, P, N]

def CertificateMachineBranchTasteGate_single_carrier_alignment_toEventFlow :
    CertificateMachineBranchUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (CertificateMachineBranchTasteGate_single_carrier_alignment_fields x).map
      CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist

def CertificateMachineBranchTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option CertificateMachineBranchUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | K :: A :: D :: L :: G :: R :: S :: H :: C :: P :: N :: [] =>
      some
        (CertificateMachineBranchUp.branch
          (CertificateMachineBranchTasteGate_single_carrier_alignment_decodeBHist K)
          (CertificateMachineBranchTasteGate_single_carrier_alignment_decodeBHist A)
          (CertificateMachineBranchTasteGate_single_carrier_alignment_decodeBHist D)
          (CertificateMachineBranchTasteGate_single_carrier_alignment_decodeBHist L)
          (CertificateMachineBranchTasteGate_single_carrier_alignment_decodeBHist G)
          (CertificateMachineBranchTasteGate_single_carrier_alignment_decodeBHist R)
          (CertificateMachineBranchTasteGate_single_carrier_alignment_decodeBHist S)
          (CertificateMachineBranchTasteGate_single_carrier_alignment_decodeBHist H)
          (CertificateMachineBranchTasteGate_single_carrier_alignment_decodeBHist C)
          (CertificateMachineBranchTasteGate_single_carrier_alignment_decodeBHist P)
          (CertificateMachineBranchTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem CertificateMachineBranchTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CertificateMachineBranchUp,
      CertificateMachineBranchTasteGate_single_carrier_alignment_fromEventFlow
          (CertificateMachineBranchTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | branch K A D L G R S H C P N =>
      change
        some
          (CertificateMachineBranchUp.branch
            (CertificateMachineBranchTasteGate_single_carrier_alignment_decodeBHist
              (CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist K))
            (CertificateMachineBranchTasteGate_single_carrier_alignment_decodeBHist
              (CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist A))
            (CertificateMachineBranchTasteGate_single_carrier_alignment_decodeBHist
              (CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist D))
            (CertificateMachineBranchTasteGate_single_carrier_alignment_decodeBHist
              (CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist L))
            (CertificateMachineBranchTasteGate_single_carrier_alignment_decodeBHist
              (CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist G))
            (CertificateMachineBranchTasteGate_single_carrier_alignment_decodeBHist
              (CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist R))
            (CertificateMachineBranchTasteGate_single_carrier_alignment_decodeBHist
              (CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist S))
            (CertificateMachineBranchTasteGate_single_carrier_alignment_decodeBHist
              (CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist H))
            (CertificateMachineBranchTasteGate_single_carrier_alignment_decodeBHist
              (CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist C))
            (CertificateMachineBranchTasteGate_single_carrier_alignment_decodeBHist
              (CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist P))
            (CertificateMachineBranchTasteGate_single_carrier_alignment_decodeBHist
              (CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (CertificateMachineBranchUp.branch K A D L G R S H C P N)
      rw [CertificateMachineBranchTasteGate_single_carrier_alignment_decode_encode K,
        CertificateMachineBranchTasteGate_single_carrier_alignment_decode_encode A,
        CertificateMachineBranchTasteGate_single_carrier_alignment_decode_encode D,
        CertificateMachineBranchTasteGate_single_carrier_alignment_decode_encode L,
        CertificateMachineBranchTasteGate_single_carrier_alignment_decode_encode G,
        CertificateMachineBranchTasteGate_single_carrier_alignment_decode_encode R,
        CertificateMachineBranchTasteGate_single_carrier_alignment_decode_encode S,
        CertificateMachineBranchTasteGate_single_carrier_alignment_decode_encode H,
        CertificateMachineBranchTasteGate_single_carrier_alignment_decode_encode C,
        CertificateMachineBranchTasteGate_single_carrier_alignment_decode_encode P,
        CertificateMachineBranchTasteGate_single_carrier_alignment_decode_encode N]

private theorem CertificateMachineBranchTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CertificateMachineBranchUp} :
    CertificateMachineBranchTasteGate_single_carrier_alignment_toEventFlow x =
        CertificateMachineBranchTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          CertificateMachineBranchTasteGate_single_carrier_alignment_fromEventFlow
            (CertificateMachineBranchTasteGate_single_carrier_alignment_toEventFlow x) :=
        (CertificateMachineBranchTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          CertificateMachineBranchTasteGate_single_carrier_alignment_fromEventFlow
            (CertificateMachineBranchTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg CertificateMachineBranchTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := CertificateMachineBranchTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem CertificateMachineBranchTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CertificateMachineBranchUp,
      CertificateMachineBranchTasteGate_single_carrier_alignment_fields x =
          CertificateMachineBranchTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | branch K₁ A₁ D₁ L₁ G₁ R₁ S₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | branch K₂ A₂ D₂ L₂ G₂ R₂ S₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance CertificateMachineBranchTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier CertificateMachineBranchUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CertificateMachineBranchTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CertificateMachineBranchTasteGate_single_carrier_alignment_fromEventFlow

instance taste_gate : ChapterTasteGate CertificateMachineBranchUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CertificateMachineBranchTasteGate_single_carrier_alignment_fromEventFlow
          (CertificateMachineBranchTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact CertificateMachineBranchTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CertificateMachineBranchTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance CertificateMachineBranchTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful CertificateMachineBranchUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := CertificateMachineBranchTasteGate_single_carrier_alignment_fields
  field_faithful := CertificateMachineBranchTasteGate_single_carrier_alignment_field_faithful

instance CertificateMachineBranchTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial CertificateMachineBranchUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CertificateMachineBranchUp.branch BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CertificateMachineBranchUp.branch (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem CertificateMachineBranchTasteGate_single_carrier_alignment
    (K A D L G R S H C P N : BHist) :
    Cont K A D →
      Cont L G R →
        UnaryHistory K →
          CertificateMachineBranchTasteGate_single_carrier_alignment_fields
              (CertificateMachineBranchUp.branch K A D L G R S H C P N) =
            [K, A, D, L, G, R, S, H, C, P, N] ∧
            CertificateMachineBranchTasteGate_single_carrier_alignment_toEventFlow
                (CertificateMachineBranchUp.branch K A D L G R S H C P N) =
              [CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist K,
                CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist A,
                CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist D,
                CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist L,
                CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist G,
                CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist R,
                CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist S,
                CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist H,
                CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist C,
                CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist P,
                CertificateMachineBranchTasteGate_single_carrier_alignment_encodeBHist N] := by
  -- BEDC touchpoint anchor: BHist BMark Cont UnaryHistory ChapterTasteGate
  intro _kernelAdmission _branchLedger _kernelUnary
  exact ⟨rfl, rfl⟩

end BEDC.Derived.CertificateMachineBranchUp.TasteGate
