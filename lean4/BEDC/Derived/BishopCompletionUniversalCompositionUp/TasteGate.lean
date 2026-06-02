import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCompletionUniversalCompositionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCompletionUniversalCompositionUp : Type where
  | mk (U V E F R S D H T P N : BHist) : BishopCompletionUniversalCompositionUp
  deriving DecidableEq

def bishopCompletionUniversalCompositionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCompletionUniversalCompositionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCompletionUniversalCompositionEncodeBHist h

def bishopCompletionUniversalCompositionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCompletionUniversalCompositionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCompletionUniversalCompositionDecodeBHist tail)

private theorem BishopCompletionUniversalCompositionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bishopCompletionUniversalCompositionDecodeBHist
          (bishopCompletionUniversalCompositionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCompletionUniversalCompositionFields :
    BishopCompletionUniversalCompositionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCompletionUniversalCompositionUp.mk U V E F R S D H T P N =>
      [U, V, E, F, R, S, D, H, T, P, N]

def bishopCompletionUniversalCompositionToEventFlow :
    BishopCompletionUniversalCompositionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (bishopCompletionUniversalCompositionFields x).map
        bishopCompletionUniversalCompositionEncodeBHist

private def bishopCompletionUniversalCompositionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bishopCompletionUniversalCompositionEventAt index rest

def bishopCompletionUniversalCompositionFromEventFlow
    (ef : EventFlow) : Option BishopCompletionUniversalCompositionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopCompletionUniversalCompositionUp.mk
      (bishopCompletionUniversalCompositionDecodeBHist
        (bishopCompletionUniversalCompositionEventAt 0 ef))
      (bishopCompletionUniversalCompositionDecodeBHist
        (bishopCompletionUniversalCompositionEventAt 1 ef))
      (bishopCompletionUniversalCompositionDecodeBHist
        (bishopCompletionUniversalCompositionEventAt 2 ef))
      (bishopCompletionUniversalCompositionDecodeBHist
        (bishopCompletionUniversalCompositionEventAt 3 ef))
      (bishopCompletionUniversalCompositionDecodeBHist
        (bishopCompletionUniversalCompositionEventAt 4 ef))
      (bishopCompletionUniversalCompositionDecodeBHist
        (bishopCompletionUniversalCompositionEventAt 5 ef))
      (bishopCompletionUniversalCompositionDecodeBHist
        (bishopCompletionUniversalCompositionEventAt 6 ef))
      (bishopCompletionUniversalCompositionDecodeBHist
        (bishopCompletionUniversalCompositionEventAt 7 ef))
      (bishopCompletionUniversalCompositionDecodeBHist
        (bishopCompletionUniversalCompositionEventAt 8 ef))
      (bishopCompletionUniversalCompositionDecodeBHist
        (bishopCompletionUniversalCompositionEventAt 9 ef))
      (bishopCompletionUniversalCompositionDecodeBHist
        (bishopCompletionUniversalCompositionEventAt 10 ef)))

private theorem BishopCompletionUniversalCompositionTasteGate_single_carrier_alignment_round_trip
    (x : BishopCompletionUniversalCompositionUp) :
    bishopCompletionUniversalCompositionFromEventFlow
        (bishopCompletionUniversalCompositionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk U V E F R S D H T P N =>
      change
        some
          (BishopCompletionUniversalCompositionUp.mk
            (bishopCompletionUniversalCompositionDecodeBHist
              (bishopCompletionUniversalCompositionEncodeBHist U))
            (bishopCompletionUniversalCompositionDecodeBHist
              (bishopCompletionUniversalCompositionEncodeBHist V))
            (bishopCompletionUniversalCompositionDecodeBHist
              (bishopCompletionUniversalCompositionEncodeBHist E))
            (bishopCompletionUniversalCompositionDecodeBHist
              (bishopCompletionUniversalCompositionEncodeBHist F))
            (bishopCompletionUniversalCompositionDecodeBHist
              (bishopCompletionUniversalCompositionEncodeBHist R))
            (bishopCompletionUniversalCompositionDecodeBHist
              (bishopCompletionUniversalCompositionEncodeBHist S))
            (bishopCompletionUniversalCompositionDecodeBHist
              (bishopCompletionUniversalCompositionEncodeBHist D))
            (bishopCompletionUniversalCompositionDecodeBHist
              (bishopCompletionUniversalCompositionEncodeBHist H))
            (bishopCompletionUniversalCompositionDecodeBHist
              (bishopCompletionUniversalCompositionEncodeBHist T))
            (bishopCompletionUniversalCompositionDecodeBHist
              (bishopCompletionUniversalCompositionEncodeBHist P))
            (bishopCompletionUniversalCompositionDecodeBHist
              (bishopCompletionUniversalCompositionEncodeBHist N))) =
          some (BishopCompletionUniversalCompositionUp.mk U V E F R S D H T P N)
      rw [
        BishopCompletionUniversalCompositionTasteGate_single_carrier_alignment_decode_encode U,
        BishopCompletionUniversalCompositionTasteGate_single_carrier_alignment_decode_encode V,
        BishopCompletionUniversalCompositionTasteGate_single_carrier_alignment_decode_encode E,
        BishopCompletionUniversalCompositionTasteGate_single_carrier_alignment_decode_encode F,
        BishopCompletionUniversalCompositionTasteGate_single_carrier_alignment_decode_encode R,
        BishopCompletionUniversalCompositionTasteGate_single_carrier_alignment_decode_encode S,
        BishopCompletionUniversalCompositionTasteGate_single_carrier_alignment_decode_encode D,
        BishopCompletionUniversalCompositionTasteGate_single_carrier_alignment_decode_encode H,
        BishopCompletionUniversalCompositionTasteGate_single_carrier_alignment_decode_encode T,
        BishopCompletionUniversalCompositionTasteGate_single_carrier_alignment_decode_encode P,
        BishopCompletionUniversalCompositionTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopCompletionUniversalCompositionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopCompletionUniversalCompositionUp} :
    bishopCompletionUniversalCompositionToEventFlow x =
        bishopCompletionUniversalCompositionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCompletionUniversalCompositionFromEventFlow
          (bishopCompletionUniversalCompositionToEventFlow x) =
        bishopCompletionUniversalCompositionFromEventFlow
          (bishopCompletionUniversalCompositionToEventFlow y) :=
    congrArg bishopCompletionUniversalCompositionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopCompletionUniversalCompositionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopCompletionUniversalCompositionTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopCompletionUniversalCompositionTasteGate_single_carrier_alignment_fields :
    ∀ x y : BishopCompletionUniversalCompositionUp,
      bishopCompletionUniversalCompositionFields x =
          bishopCompletionUniversalCompositionFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U1 V1 E1 F1 R1 S1 D1 H1 T1 P1 N1 =>
      cases y with
      | mk U2 V2 E2 F2 R2 S2 D2 H2 T2 P2 N2 =>
          cases hfields
          rfl

instance bishopCompletionUniversalCompositionBHistCarrier :
    BHistCarrier BishopCompletionUniversalCompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCompletionUniversalCompositionToEventFlow
  fromEventFlow := bishopCompletionUniversalCompositionFromEventFlow

instance bishopCompletionUniversalCompositionChapterTasteGate :
    ChapterTasteGate BishopCompletionUniversalCompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopCompletionUniversalCompositionFromEventFlow
          (bishopCompletionUniversalCompositionToEventFlow x) =
        some x
    exact BishopCompletionUniversalCompositionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopCompletionUniversalCompositionTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance bishopCompletionUniversalCompositionFieldFaithful :
    FieldFaithful BishopCompletionUniversalCompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopCompletionUniversalCompositionFields
  field_faithful :=
    BishopCompletionUniversalCompositionTasteGate_single_carrier_alignment_fields

instance bishopCompletionUniversalCompositionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BishopCompletionUniversalCompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopCompletionUniversalCompositionUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      BishopCompletionUniversalCompositionUp.mk (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BishopCompletionUniversalCompositionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BishopCompletionUniversalCompositionUp) ∧
      Nonempty (FieldFaithful BishopCompletionUniversalCompositionUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial BishopCompletionUniversalCompositionUp) ∧
      (∀ h : BHist,
        bishopCompletionUniversalCompositionDecodeBHist
            (bishopCompletionUniversalCompositionEncodeBHist h) =
          h) ∧
      (∀ x : BishopCompletionUniversalCompositionUp,
        bishopCompletionUniversalCompositionFromEventFlow
            (bishopCompletionUniversalCompositionToEventFlow x) =
          some x) ∧
      (∀ x y : BishopCompletionUniversalCompositionUp,
        bishopCompletionUniversalCompositionToEventFlow x =
            bishopCompletionUniversalCompositionToEventFlow y →
          x = y) ∧
      bishopCompletionUniversalCompositionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨bishopCompletionUniversalCompositionChapterTasteGate⟩,
      ⟨bishopCompletionUniversalCompositionFieldFaithful⟩,
      ⟨bishopCompletionUniversalCompositionNontrivial⟩,
      BishopCompletionUniversalCompositionTasteGate_single_carrier_alignment_decode_encode,
      BishopCompletionUniversalCompositionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BishopCompletionUniversalCompositionTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.BishopCompletionUniversalCompositionUp
