import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProjectiveVarUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProjectiveVarUp : Type where
  | mk
      (chart affinePatch homogeneousPolynomial projectiveEnvelope zeroLocus scopedPrimitive
        localNameCert : BHist) :
        ProjectiveVarUp
  deriving DecidableEq

def ProjectiveVarTasteGate_single_carrier_alignment_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b0]

def ProjectiveVarTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ProjectiveVarTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: ProjectiveVarTasteGate_single_carrier_alignment_encodeBHist h

def ProjectiveVarTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (ProjectiveVarTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (ProjectiveVarTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem ProjectiveVarTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      ProjectiveVarTasteGate_single_carrier_alignment_decodeBHist
          (ProjectiveVarTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ProjectiveVarTasteGate_single_carrier_alignment_fields :
    ProjectiveVarUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ProjectiveVarUp.mk chart affinePatch homogeneousPolynomial projectiveEnvelope zeroLocus
      scopedPrimitive localNameCert =>
      [chart, affinePatch, homogeneousPolynomial, projectiveEnvelope, zeroLocus, scopedPrimitive,
        localNameCert]

def ProjectiveVarTasteGate_single_carrier_alignment_toEventFlow :
    ProjectiveVarUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ProjectiveVarUp.mk chart affinePatch homogeneousPolynomial projectiveEnvelope zeroLocus
      scopedPrimitive localNameCert =>
      [ProjectiveVarTasteGate_single_carrier_alignment_tag,
        ProjectiveVarTasteGate_single_carrier_alignment_encodeBHist chart,
        ProjectiveVarTasteGate_single_carrier_alignment_encodeBHist affinePatch,
        ProjectiveVarTasteGate_single_carrier_alignment_encodeBHist homogeneousPolynomial,
        ProjectiveVarTasteGate_single_carrier_alignment_encodeBHist projectiveEnvelope,
        ProjectiveVarTasteGate_single_carrier_alignment_encodeBHist zeroLocus,
        ProjectiveVarTasteGate_single_carrier_alignment_encodeBHist scopedPrimitive,
        ProjectiveVarTasteGate_single_carrier_alignment_encodeBHist localNameCert]

private def ProjectiveVarTasteGate_single_carrier_alignment_eventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      ProjectiveVarTasteGate_single_carrier_alignment_eventAt index rest

def ProjectiveVarTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option ProjectiveVarUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (ProjectiveVarUp.mk
          (ProjectiveVarTasteGate_single_carrier_alignment_decodeBHist
            (ProjectiveVarTasteGate_single_carrier_alignment_eventAt 1 ef))
          (ProjectiveVarTasteGate_single_carrier_alignment_decodeBHist
            (ProjectiveVarTasteGate_single_carrier_alignment_eventAt 2 ef))
          (ProjectiveVarTasteGate_single_carrier_alignment_decodeBHist
            (ProjectiveVarTasteGate_single_carrier_alignment_eventAt 3 ef))
          (ProjectiveVarTasteGate_single_carrier_alignment_decodeBHist
            (ProjectiveVarTasteGate_single_carrier_alignment_eventAt 4 ef))
          (ProjectiveVarTasteGate_single_carrier_alignment_decodeBHist
            (ProjectiveVarTasteGate_single_carrier_alignment_eventAt 5 ef))
          (ProjectiveVarTasteGate_single_carrier_alignment_decodeBHist
            (ProjectiveVarTasteGate_single_carrier_alignment_eventAt 6 ef))
          (ProjectiveVarTasteGate_single_carrier_alignment_decodeBHist
            (ProjectiveVarTasteGate_single_carrier_alignment_eventAt 7 ef)))

private theorem ProjectiveVarTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ProjectiveVarUp,
      ProjectiveVarTasteGate_single_carrier_alignment_fromEventFlow
          (ProjectiveVarTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk chart affinePatch homogeneousPolynomial projectiveEnvelope zeroLocus scopedPrimitive
      localNameCert =>
      change
        some
          (ProjectiveVarUp.mk
            (ProjectiveVarTasteGate_single_carrier_alignment_decodeBHist
              (ProjectiveVarTasteGate_single_carrier_alignment_encodeBHist chart))
            (ProjectiveVarTasteGate_single_carrier_alignment_decodeBHist
              (ProjectiveVarTasteGate_single_carrier_alignment_encodeBHist affinePatch))
            (ProjectiveVarTasteGate_single_carrier_alignment_decodeBHist
              (ProjectiveVarTasteGate_single_carrier_alignment_encodeBHist homogeneousPolynomial))
            (ProjectiveVarTasteGate_single_carrier_alignment_decodeBHist
              (ProjectiveVarTasteGate_single_carrier_alignment_encodeBHist projectiveEnvelope))
            (ProjectiveVarTasteGate_single_carrier_alignment_decodeBHist
              (ProjectiveVarTasteGate_single_carrier_alignment_encodeBHist zeroLocus))
            (ProjectiveVarTasteGate_single_carrier_alignment_decodeBHist
              (ProjectiveVarTasteGate_single_carrier_alignment_encodeBHist scopedPrimitive))
            (ProjectiveVarTasteGate_single_carrier_alignment_decodeBHist
              (ProjectiveVarTasteGate_single_carrier_alignment_encodeBHist localNameCert))) =
          some
            (ProjectiveVarUp.mk chart affinePatch homogeneousPolynomial projectiveEnvelope
              zeroLocus scopedPrimitive localNameCert)
      rw [ProjectiveVarTasteGate_single_carrier_alignment_decode_encode chart,
        ProjectiveVarTasteGate_single_carrier_alignment_decode_encode affinePatch,
        ProjectiveVarTasteGate_single_carrier_alignment_decode_encode homogeneousPolynomial,
        ProjectiveVarTasteGate_single_carrier_alignment_decode_encode projectiveEnvelope,
        ProjectiveVarTasteGate_single_carrier_alignment_decode_encode zeroLocus,
        ProjectiveVarTasteGate_single_carrier_alignment_decode_encode scopedPrimitive,
        ProjectiveVarTasteGate_single_carrier_alignment_decode_encode localNameCert]

private theorem ProjectiveVarTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ProjectiveVarUp} :
    ProjectiveVarTasteGate_single_carrier_alignment_toEventFlow x =
        ProjectiveVarTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ProjectiveVarTasteGate_single_carrier_alignment_fromEventFlow
          (ProjectiveVarTasteGate_single_carrier_alignment_toEventFlow x) =
        ProjectiveVarTasteGate_single_carrier_alignment_fromEventFlow
          (ProjectiveVarTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg ProjectiveVarTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ProjectiveVarTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ProjectiveVarTasteGate_single_carrier_alignment_round_trip y)))

private theorem ProjectiveVarTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : ProjectiveVarUp,
      ProjectiveVarTasteGate_single_carrier_alignment_fields x =
          ProjectiveVarTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk chart₁ affinePatch₁ homogeneousPolynomial₁ projectiveEnvelope₁ zeroLocus₁
      scopedPrimitive₁ localNameCert₁ =>
      cases y with
      | mk chart₂ affinePatch₂ homogeneousPolynomial₂ projectiveEnvelope₂ zeroLocus₂
          scopedPrimitive₂ localNameCert₂ =>
          cases hfields
          rfl

instance ProjectiveVarTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier ProjectiveVarUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ProjectiveVarTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := ProjectiveVarTasteGate_single_carrier_alignment_fromEventFlow

instance ProjectiveVarTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate ProjectiveVarUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      ProjectiveVarTasteGate_single_carrier_alignment_fromEventFlow
          (ProjectiveVarTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact ProjectiveVarTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ProjectiveVarTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance ProjectiveVarTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful ProjectiveVarUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := ProjectiveVarTasteGate_single_carrier_alignment_fields
  field_faithful := ProjectiveVarTasteGate_single_carrier_alignment_fields_faithful

theorem ProjectiveVarTasteGate_single_carrier_alignment :
    (forall h : BHist,
      ProjectiveVarTasteGate_single_carrier_alignment_decodeBHist
          (ProjectiveVarTasteGate_single_carrier_alignment_encodeBHist h) =
        h) /\
      ProjectiveVarTasteGate_single_carrier_alignment_fields
          (ProjectiveVarUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty] /\
        ProjectiveVarTasteGate_single_carrier_alignment_toEventFlow
            (ProjectiveVarUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty) =
          [[BMark.b1, BMark.b0], [], [], [], [], [], [], []] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ProjectiveVarTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · rfl
    · rfl

end BEDC.Derived.ProjectiveVarUp
