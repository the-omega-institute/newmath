import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedLamDomainSubjectReductionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedLamDomainSubjectReductionUp : Type where
  | mk (T D D' B Y Z G H R Q N : BHist) : ClosedLamDomainSubjectReductionUp
  deriving DecidableEq

def closedLamDomainSubjectReductionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedLamDomainSubjectReductionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedLamDomainSubjectReductionEncodeBHist h

def closedLamDomainSubjectReductionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedLamDomainSubjectReductionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedLamDomainSubjectReductionDecodeBHist tail)

private theorem closedLamDomainSubjectReduction_decode_encode_bhist :
    ∀ h : BHist,
      closedLamDomainSubjectReductionDecodeBHist
        (closedLamDomainSubjectReductionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedLamDomainSubjectReductionFields :
    ClosedLamDomainSubjectReductionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedLamDomainSubjectReductionUp.mk T D D' B Y Z G H R Q N =>
      [T, D, D', B, Y, Z, G, H, R, Q, N]

def closedLamDomainSubjectReductionToEventFlow :
    ClosedLamDomainSubjectReductionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (closedLamDomainSubjectReductionFields x).map
        closedLamDomainSubjectReductionEncodeBHist

private def closedLamDomainSubjectReductionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => closedLamDomainSubjectReductionEventAt index rest

def closedLamDomainSubjectReductionFromEventFlow
    (ef : EventFlow) : Option ClosedLamDomainSubjectReductionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClosedLamDomainSubjectReductionUp.mk
      (closedLamDomainSubjectReductionDecodeBHist
        (closedLamDomainSubjectReductionEventAt 0 ef))
      (closedLamDomainSubjectReductionDecodeBHist
        (closedLamDomainSubjectReductionEventAt 1 ef))
      (closedLamDomainSubjectReductionDecodeBHist
        (closedLamDomainSubjectReductionEventAt 2 ef))
      (closedLamDomainSubjectReductionDecodeBHist
        (closedLamDomainSubjectReductionEventAt 3 ef))
      (closedLamDomainSubjectReductionDecodeBHist
        (closedLamDomainSubjectReductionEventAt 4 ef))
      (closedLamDomainSubjectReductionDecodeBHist
        (closedLamDomainSubjectReductionEventAt 5 ef))
      (closedLamDomainSubjectReductionDecodeBHist
        (closedLamDomainSubjectReductionEventAt 6 ef))
      (closedLamDomainSubjectReductionDecodeBHist
        (closedLamDomainSubjectReductionEventAt 7 ef))
      (closedLamDomainSubjectReductionDecodeBHist
        (closedLamDomainSubjectReductionEventAt 8 ef))
      (closedLamDomainSubjectReductionDecodeBHist
        (closedLamDomainSubjectReductionEventAt 9 ef))
      (closedLamDomainSubjectReductionDecodeBHist
        (closedLamDomainSubjectReductionEventAt 10 ef)))

private theorem closedLamDomainSubjectReduction_round_trip :
    ∀ x : ClosedLamDomainSubjectReductionUp,
      closedLamDomainSubjectReductionFromEventFlow
        (closedLamDomainSubjectReductionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T D D' B Y Z G H R Q N =>
      change
        some
          (ClosedLamDomainSubjectReductionUp.mk
            (closedLamDomainSubjectReductionDecodeBHist
              (closedLamDomainSubjectReductionEncodeBHist T))
            (closedLamDomainSubjectReductionDecodeBHist
              (closedLamDomainSubjectReductionEncodeBHist D))
            (closedLamDomainSubjectReductionDecodeBHist
              (closedLamDomainSubjectReductionEncodeBHist D'))
            (closedLamDomainSubjectReductionDecodeBHist
              (closedLamDomainSubjectReductionEncodeBHist B))
            (closedLamDomainSubjectReductionDecodeBHist
              (closedLamDomainSubjectReductionEncodeBHist Y))
            (closedLamDomainSubjectReductionDecodeBHist
              (closedLamDomainSubjectReductionEncodeBHist Z))
            (closedLamDomainSubjectReductionDecodeBHist
              (closedLamDomainSubjectReductionEncodeBHist G))
            (closedLamDomainSubjectReductionDecodeBHist
              (closedLamDomainSubjectReductionEncodeBHist H))
            (closedLamDomainSubjectReductionDecodeBHist
              (closedLamDomainSubjectReductionEncodeBHist R))
            (closedLamDomainSubjectReductionDecodeBHist
              (closedLamDomainSubjectReductionEncodeBHist Q))
            (closedLamDomainSubjectReductionDecodeBHist
              (closedLamDomainSubjectReductionEncodeBHist N))) =
          some (ClosedLamDomainSubjectReductionUp.mk T D D' B Y Z G H R Q N)
      rw [closedLamDomainSubjectReduction_decode_encode_bhist T,
        closedLamDomainSubjectReduction_decode_encode_bhist D,
        closedLamDomainSubjectReduction_decode_encode_bhist D',
        closedLamDomainSubjectReduction_decode_encode_bhist B,
        closedLamDomainSubjectReduction_decode_encode_bhist Y,
        closedLamDomainSubjectReduction_decode_encode_bhist Z,
        closedLamDomainSubjectReduction_decode_encode_bhist G,
        closedLamDomainSubjectReduction_decode_encode_bhist H,
        closedLamDomainSubjectReduction_decode_encode_bhist R,
        closedLamDomainSubjectReduction_decode_encode_bhist Q,
        closedLamDomainSubjectReduction_decode_encode_bhist N]

private theorem closedLamDomainSubjectReductionToEventFlow_injective
    {x y : ClosedLamDomainSubjectReductionUp} :
    closedLamDomainSubjectReductionToEventFlow x =
      closedLamDomainSubjectReductionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedLamDomainSubjectReductionFromEventFlow
          (closedLamDomainSubjectReductionToEventFlow x) =
        closedLamDomainSubjectReductionFromEventFlow
          (closedLamDomainSubjectReductionToEventFlow y) :=
    congrArg closedLamDomainSubjectReductionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closedLamDomainSubjectReduction_round_trip x).symm
      (Eq.trans hread (closedLamDomainSubjectReduction_round_trip y)))

private theorem closedLamDomainSubjectReduction_field_faithful :
    ∀ x y : ClosedLamDomainSubjectReductionUp,
      closedLamDomainSubjectReductionFields x =
        closedLamDomainSubjectReductionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 D1 Dp1 B1 Y1 Z1 G1 H1 R1 Q1 N1 =>
      cases y with
      | mk T2 D2 Dp2 B2 Y2 Z2 G2 H2 R2 Q2 N2 =>
          cases hfields
          rfl

instance closedLamDomainSubjectReductionBHistCarrier :
    BHistCarrier ClosedLamDomainSubjectReductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedLamDomainSubjectReductionToEventFlow
  fromEventFlow := closedLamDomainSubjectReductionFromEventFlow

instance closedLamDomainSubjectReductionChapterTasteGate :
    ChapterTasteGate ClosedLamDomainSubjectReductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedLamDomainSubjectReductionFromEventFlow
        (closedLamDomainSubjectReductionToEventFlow x) = some x
    exact closedLamDomainSubjectReduction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedLamDomainSubjectReductionToEventFlow_injective heq)

instance closedLamDomainSubjectReductionFieldFaithful :
    FieldFaithful ClosedLamDomainSubjectReductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedLamDomainSubjectReductionFields
  field_faithful := closedLamDomainSubjectReduction_field_faithful

instance closedLamDomainSubjectReductionNontrivial :
    Nontrivial ClosedLamDomainSubjectReductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedLamDomainSubjectReductionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      ClosedLamDomainSubjectReductionUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ClosedLamDomainSubjectReductionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedLamDomainSubjectReductionChapterTasteGate

theorem ClosedLamDomainSubjectReductionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      closedLamDomainSubjectReductionDecodeBHist
        (closedLamDomainSubjectReductionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ClosedLamDomainSubjectReductionUp) ∧
        Nonempty (ChapterTasteGate ClosedLamDomainSubjectReductionUp) ∧
          closedLamDomainSubjectReductionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨closedLamDomainSubjectReduction_decode_encode_bhist,
      ⟨closedLamDomainSubjectReductionBHistCarrier⟩,
      ⟨closedLamDomainSubjectReductionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.ClosedLamDomainSubjectReductionUp
