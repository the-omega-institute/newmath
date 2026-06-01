import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedPiDomainSubjectReductionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedPiDomainSubjectReductionUp : Type where
  | mk (T D D' C Y Z B H R Q N : BHist) : ClosedPiDomainSubjectReductionUp
  deriving DecidableEq

def closedPiDomainSubjectReductionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedPiDomainSubjectReductionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedPiDomainSubjectReductionEncodeBHist h

def closedPiDomainSubjectReductionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedPiDomainSubjectReductionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedPiDomainSubjectReductionDecodeBHist tail)

private def ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_rawAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, head :: _ => head
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest =>
      ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_rawAt n rest

private theorem ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      closedPiDomainSubjectReductionDecodeBHist
          (closedPiDomainSubjectReductionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedPiDomainSubjectReductionFields :
    ClosedPiDomainSubjectReductionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedPiDomainSubjectReductionUp.mk T D D' C Y Z B H R Q N =>
      [T, D, D', C, Y, Z, B, H, R, Q, N]

def closedPiDomainSubjectReductionToEventFlow :
    ClosedPiDomainSubjectReductionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedPiDomainSubjectReductionUp.mk T D D' C Y Z B H R Q N =>
      [closedPiDomainSubjectReductionEncodeBHist T,
        closedPiDomainSubjectReductionEncodeBHist D,
        closedPiDomainSubjectReductionEncodeBHist D',
        closedPiDomainSubjectReductionEncodeBHist C,
        closedPiDomainSubjectReductionEncodeBHist Y,
        closedPiDomainSubjectReductionEncodeBHist Z,
        closedPiDomainSubjectReductionEncodeBHist B,
        closedPiDomainSubjectReductionEncodeBHist H,
        closedPiDomainSubjectReductionEncodeBHist R,
        closedPiDomainSubjectReductionEncodeBHist Q,
        closedPiDomainSubjectReductionEncodeBHist N]

def closedPiDomainSubjectReductionFromEventFlow :
    EventFlow → Option ClosedPiDomainSubjectReductionUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (ClosedPiDomainSubjectReductionUp.mk
          (closedPiDomainSubjectReductionDecodeBHist
            (ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_rawAt 0 ef))
          (closedPiDomainSubjectReductionDecodeBHist
            (ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_rawAt 1 ef))
          (closedPiDomainSubjectReductionDecodeBHist
            (ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_rawAt 2 ef))
          (closedPiDomainSubjectReductionDecodeBHist
            (ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_rawAt 3 ef))
          (closedPiDomainSubjectReductionDecodeBHist
            (ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_rawAt 4 ef))
          (closedPiDomainSubjectReductionDecodeBHist
            (ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_rawAt 5 ef))
          (closedPiDomainSubjectReductionDecodeBHist
            (ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_rawAt 6 ef))
          (closedPiDomainSubjectReductionDecodeBHist
            (ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_rawAt 7 ef))
          (closedPiDomainSubjectReductionDecodeBHist
            (ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_rawAt 8 ef))
          (closedPiDomainSubjectReductionDecodeBHist
            (ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_rawAt 9 ef))
          (closedPiDomainSubjectReductionDecodeBHist
            (ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_rawAt 10 ef)))

private theorem ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ClosedPiDomainSubjectReductionUp,
      closedPiDomainSubjectReductionFromEventFlow
          (closedPiDomainSubjectReductionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T D D' C Y Z B H R Q N =>
      change
        some
          (ClosedPiDomainSubjectReductionUp.mk
            (closedPiDomainSubjectReductionDecodeBHist
              (closedPiDomainSubjectReductionEncodeBHist T))
            (closedPiDomainSubjectReductionDecodeBHist
              (closedPiDomainSubjectReductionEncodeBHist D))
            (closedPiDomainSubjectReductionDecodeBHist
              (closedPiDomainSubjectReductionEncodeBHist D'))
            (closedPiDomainSubjectReductionDecodeBHist
              (closedPiDomainSubjectReductionEncodeBHist C))
            (closedPiDomainSubjectReductionDecodeBHist
              (closedPiDomainSubjectReductionEncodeBHist Y))
            (closedPiDomainSubjectReductionDecodeBHist
              (closedPiDomainSubjectReductionEncodeBHist Z))
            (closedPiDomainSubjectReductionDecodeBHist
              (closedPiDomainSubjectReductionEncodeBHist B))
            (closedPiDomainSubjectReductionDecodeBHist
              (closedPiDomainSubjectReductionEncodeBHist H))
            (closedPiDomainSubjectReductionDecodeBHist
              (closedPiDomainSubjectReductionEncodeBHist R))
            (closedPiDomainSubjectReductionDecodeBHist
              (closedPiDomainSubjectReductionEncodeBHist Q))
            (closedPiDomainSubjectReductionDecodeBHist
              (closedPiDomainSubjectReductionEncodeBHist N))) =
          some (ClosedPiDomainSubjectReductionUp.mk T D D' C Y Z B H R Q N)
      rw [ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_decode T,
        ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_decode D,
        ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_decode D',
        ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_decode C,
        ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_decode Y,
        ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_decode Z,
        ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_decode B,
        ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_decode H,
        ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_decode R,
        ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_decode Q,
        ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_decode N]

private theorem ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_injective
    {x y : ClosedPiDomainSubjectReductionUp} :
    closedPiDomainSubjectReductionToEventFlow x =
        closedPiDomainSubjectReductionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedPiDomainSubjectReductionFromEventFlow
          (closedPiDomainSubjectReductionToEventFlow x) =
        closedPiDomainSubjectReductionFromEventFlow
          (closedPiDomainSubjectReductionToEventFlow y) :=
    congrArg closedPiDomainSubjectReductionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_round_trip y)))

private theorem ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_fields :
    ∀ x y : ClosedPiDomainSubjectReductionUp,
      closedPiDomainSubjectReductionFields x = closedPiDomainSubjectReductionFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T₁ D₁ D'₁ C₁ Y₁ Z₁ B₁ H₁ R₁ Q₁ N₁ =>
      cases y with
      | mk T₂ D₂ D'₂ C₂ Y₂ Z₂ B₂ H₂ R₂ Q₂ N₂ =>
          cases hfields
          rfl

instance closedPiDomainSubjectReductionBHistCarrier :
    BHistCarrier ClosedPiDomainSubjectReductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedPiDomainSubjectReductionToEventFlow
  fromEventFlow := closedPiDomainSubjectReductionFromEventFlow

instance closedPiDomainSubjectReductionChapterTasteGate :
    ChapterTasteGate ClosedPiDomainSubjectReductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedPiDomainSubjectReductionFromEventFlow
          (closedPiDomainSubjectReductionToEventFlow x) =
        some x
    exact ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_injective heq)

instance closedPiDomainSubjectReductionFieldFaithful :
    FieldFaithful ClosedPiDomainSubjectReductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedPiDomainSubjectReductionFields
  field_faithful := ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_fields

instance closedPiDomainSubjectReductionNontrivial :
    Nontrivial ClosedPiDomainSubjectReductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedPiDomainSubjectReductionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ClosedPiDomainSubjectReductionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ClosedPiDomainSubjectReductionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedPiDomainSubjectReductionChapterTasteGate

theorem ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      closedPiDomainSubjectReductionDecodeBHist
          (closedPiDomainSubjectReductionEncodeBHist h) =
        h) ∧
      (∀ x : ClosedPiDomainSubjectReductionUp,
        closedPiDomainSubjectReductionFromEventFlow
            (closedPiDomainSubjectReductionToEventFlow x) =
          some x) ∧
        (∀ x y : ClosedPiDomainSubjectReductionUp,
          closedPiDomainSubjectReductionToEventFlow x =
              closedPiDomainSubjectReductionToEventFlow y →
            x = y) ∧
          closedPiDomainSubjectReductionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_decode,
      ⟨ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_round_trip,
        ⟨fun _x _y heq =>
            ClosedPiDomainSubjectReductionTasteGate_single_carrier_alignment_injective heq,
          rfl⟩⟩⟩

end BEDC.Derived.ClosedPiDomainSubjectReductionUp
