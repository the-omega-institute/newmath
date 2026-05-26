import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRealCauchyCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRealCauchyCriterionUp : Type where
  | mk (L S R D Q E H C P N : BHist) : LocatedRealCauchyCriterionUp
  deriving DecidableEq

def locatedRealCauchyCriterionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRealCauchyCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRealCauchyCriterionEncodeBHist h

def locatedRealCauchyCriterionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRealCauchyCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRealCauchyCriterionDecodeBHist tail)

private theorem LocatedRealCauchyCriterionTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      locatedRealCauchyCriterionDecodeBHist
          (locatedRealCauchyCriterionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedRealCauchyCriterionFields :
    LocatedRealCauchyCriterionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealCauchyCriterionUp.mk L S R D Q E H C P N => [L, S, R, D, Q, E, H, C, P, N]

def locatedRealCauchyCriterionToEventFlow :
    LocatedRealCauchyCriterionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => locatedRealCauchyCriterionFields x |>.map locatedRealCauchyCriterionEncodeBHist

private def locatedRealCauchyCriterionRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => locatedRealCauchyCriterionRawAt n rest

def locatedRealCauchyCriterionFromEventFlow :
    EventFlow -> Option LocatedRealCauchyCriterionUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (LocatedRealCauchyCriterionUp.mk
          (locatedRealCauchyCriterionDecodeBHist (locatedRealCauchyCriterionRawAt 0 flow))
          (locatedRealCauchyCriterionDecodeBHist (locatedRealCauchyCriterionRawAt 1 flow))
          (locatedRealCauchyCriterionDecodeBHist (locatedRealCauchyCriterionRawAt 2 flow))
          (locatedRealCauchyCriterionDecodeBHist (locatedRealCauchyCriterionRawAt 3 flow))
          (locatedRealCauchyCriterionDecodeBHist (locatedRealCauchyCriterionRawAt 4 flow))
          (locatedRealCauchyCriterionDecodeBHist (locatedRealCauchyCriterionRawAt 5 flow))
          (locatedRealCauchyCriterionDecodeBHist (locatedRealCauchyCriterionRawAt 6 flow))
          (locatedRealCauchyCriterionDecodeBHist (locatedRealCauchyCriterionRawAt 7 flow))
          (locatedRealCauchyCriterionDecodeBHist (locatedRealCauchyCriterionRawAt 8 flow))
          (locatedRealCauchyCriterionDecodeBHist (locatedRealCauchyCriterionRawAt 9 flow)))

private theorem LocatedRealCauchyCriterionTasteGate_single_carrier_alignment_round_trip
    (x : LocatedRealCauchyCriterionUp) :
    locatedRealCauchyCriterionFromEventFlow
        (locatedRealCauchyCriterionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L S R D Q E H C P N =>
      change
        some
          (LocatedRealCauchyCriterionUp.mk
            (locatedRealCauchyCriterionDecodeBHist
              (locatedRealCauchyCriterionEncodeBHist L))
            (locatedRealCauchyCriterionDecodeBHist
              (locatedRealCauchyCriterionEncodeBHist S))
            (locatedRealCauchyCriterionDecodeBHist
              (locatedRealCauchyCriterionEncodeBHist R))
            (locatedRealCauchyCriterionDecodeBHist
              (locatedRealCauchyCriterionEncodeBHist D))
            (locatedRealCauchyCriterionDecodeBHist
              (locatedRealCauchyCriterionEncodeBHist Q))
            (locatedRealCauchyCriterionDecodeBHist
              (locatedRealCauchyCriterionEncodeBHist E))
            (locatedRealCauchyCriterionDecodeBHist
              (locatedRealCauchyCriterionEncodeBHist H))
            (locatedRealCauchyCriterionDecodeBHist
              (locatedRealCauchyCriterionEncodeBHist C))
            (locatedRealCauchyCriterionDecodeBHist
              (locatedRealCauchyCriterionEncodeBHist P))
            (locatedRealCauchyCriterionDecodeBHist
              (locatedRealCauchyCriterionEncodeBHist N))) =
          some (LocatedRealCauchyCriterionUp.mk L S R D Q E H C P N)
      rw [LocatedRealCauchyCriterionTasteGate_single_carrier_alignment_decode_encode L,
        LocatedRealCauchyCriterionTasteGate_single_carrier_alignment_decode_encode S,
        LocatedRealCauchyCriterionTasteGate_single_carrier_alignment_decode_encode R,
        LocatedRealCauchyCriterionTasteGate_single_carrier_alignment_decode_encode D,
        LocatedRealCauchyCriterionTasteGate_single_carrier_alignment_decode_encode Q,
        LocatedRealCauchyCriterionTasteGate_single_carrier_alignment_decode_encode E,
        LocatedRealCauchyCriterionTasteGate_single_carrier_alignment_decode_encode H,
        LocatedRealCauchyCriterionTasteGate_single_carrier_alignment_decode_encode C,
        LocatedRealCauchyCriterionTasteGate_single_carrier_alignment_decode_encode P,
        LocatedRealCauchyCriterionTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocatedRealCauchyCriterionTasteGate_single_carrier_alignment_injective
    {x y : LocatedRealCauchyCriterionUp} :
    locatedRealCauchyCriterionToEventFlow x =
        locatedRealCauchyCriterionToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRealCauchyCriterionFromEventFlow
          (locatedRealCauchyCriterionToEventFlow x) =
        locatedRealCauchyCriterionFromEventFlow
          (locatedRealCauchyCriterionToEventFlow y) :=
    congrArg locatedRealCauchyCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedRealCauchyCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedRealCauchyCriterionTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatedRealCauchyCriterionTasteGate_single_carrier_alignment_fields :
    forall x y : LocatedRealCauchyCriterionUp,
      locatedRealCauchyCriterionFields x = locatedRealCauchyCriterionFields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L1 S1 R1 D1 Q1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk L2 S2 R2 D2 Q2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance locatedRealCauchyCriterionBHistCarrier :
    BHistCarrier LocatedRealCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRealCauchyCriterionToEventFlow
  fromEventFlow := locatedRealCauchyCriterionFromEventFlow

instance locatedRealCauchyCriterionChapterTasteGate :
    ChapterTasteGate LocatedRealCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedRealCauchyCriterionFromEventFlow
          (locatedRealCauchyCriterionToEventFlow x) =
        some x
    exact LocatedRealCauchyCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedRealCauchyCriterionTasteGate_single_carrier_alignment_injective heq)

instance locatedRealCauchyCriterionFieldFaithful :
    FieldFaithful LocatedRealCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedRealCauchyCriterionFields
  field_faithful := LocatedRealCauchyCriterionTasteGate_single_carrier_alignment_fields

instance locatedRealCauchyCriterionNontrivial :
    Nontrivial LocatedRealCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedRealCauchyCriterionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedRealCauchyCriterionUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedRealCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedRealCauchyCriterionChapterTasteGate

namespace TasteGate

theorem LocatedRealCauchyCriterionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier LocatedRealCauchyCriterionUp) ∧
      Nonempty (ChapterTasteGate LocatedRealCauchyCriterionUp) ∧
        Nonempty (FieldFaithful LocatedRealCauchyCriterionUp) ∧
          Nonempty (BEDC.Meta.TasteGate.Nontrivial LocatedRealCauchyCriterionUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨locatedRealCauchyCriterionBHistCarrier⟩,
      ⟨locatedRealCauchyCriterionChapterTasteGate⟩,
      ⟨locatedRealCauchyCriterionFieldFaithful⟩,
      ⟨locatedRealCauchyCriterionNontrivial⟩⟩

end TasteGate

end BEDC.Derived.LocatedRealCauchyCriterionUp
