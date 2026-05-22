import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedIntervalCauchyCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedIntervalCauchyCompletionUp : Type where
  | mk (A B I S R D Q E H C P N : BHist) : ClosedIntervalCauchyCompletionUp
  deriving DecidableEq

def closedIntervalCauchyCompletionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedIntervalCauchyCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedIntervalCauchyCompletionEncodeBHist h

def closedIntervalCauchyCompletionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedIntervalCauchyCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedIntervalCauchyCompletionDecodeBHist tail)

private theorem ClosedIntervalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      closedIntervalCauchyCompletionDecodeBHist
          (closedIntervalCauchyCompletionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedIntervalCauchyCompletionFields :
    ClosedIntervalCauchyCompletionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedIntervalCauchyCompletionUp.mk A B I S R D Q E H C P N =>
      [A, B, I, S, R, D, Q, E, H, C, P, N]

def closedIntervalCauchyCompletionToEventFlow :
    ClosedIntervalCauchyCompletionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (closedIntervalCauchyCompletionFields x).map
      closedIntervalCauchyCompletionEncodeBHist

private def closedIntervalCauchyCompletionRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => closedIntervalCauchyCompletionRawAt index rest

def closedIntervalCauchyCompletionFromEventFlow
    (flow : EventFlow) : Option ClosedIntervalCauchyCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClosedIntervalCauchyCompletionUp.mk
      (closedIntervalCauchyCompletionDecodeBHist
        (closedIntervalCauchyCompletionRawAt 0 flow))
      (closedIntervalCauchyCompletionDecodeBHist
        (closedIntervalCauchyCompletionRawAt 1 flow))
      (closedIntervalCauchyCompletionDecodeBHist
        (closedIntervalCauchyCompletionRawAt 2 flow))
      (closedIntervalCauchyCompletionDecodeBHist
        (closedIntervalCauchyCompletionRawAt 3 flow))
      (closedIntervalCauchyCompletionDecodeBHist
        (closedIntervalCauchyCompletionRawAt 4 flow))
      (closedIntervalCauchyCompletionDecodeBHist
        (closedIntervalCauchyCompletionRawAt 5 flow))
      (closedIntervalCauchyCompletionDecodeBHist
        (closedIntervalCauchyCompletionRawAt 6 flow))
      (closedIntervalCauchyCompletionDecodeBHist
        (closedIntervalCauchyCompletionRawAt 7 flow))
      (closedIntervalCauchyCompletionDecodeBHist
        (closedIntervalCauchyCompletionRawAt 8 flow))
      (closedIntervalCauchyCompletionDecodeBHist
        (closedIntervalCauchyCompletionRawAt 9 flow))
      (closedIntervalCauchyCompletionDecodeBHist
        (closedIntervalCauchyCompletionRawAt 10 flow))
      (closedIntervalCauchyCompletionDecodeBHist
        (closedIntervalCauchyCompletionRawAt 11 flow)))

private theorem ClosedIntervalCauchyCompletionTasteGate_single_carrier_alignment_round_trip :
    forall x : ClosedIntervalCauchyCompletionUp,
      closedIntervalCauchyCompletionFromEventFlow
          (closedIntervalCauchyCompletionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B I S R D Q E H C P N =>
      change
        some
          (ClosedIntervalCauchyCompletionUp.mk
            (closedIntervalCauchyCompletionDecodeBHist
              (closedIntervalCauchyCompletionEncodeBHist A))
            (closedIntervalCauchyCompletionDecodeBHist
              (closedIntervalCauchyCompletionEncodeBHist B))
            (closedIntervalCauchyCompletionDecodeBHist
              (closedIntervalCauchyCompletionEncodeBHist I))
            (closedIntervalCauchyCompletionDecodeBHist
              (closedIntervalCauchyCompletionEncodeBHist S))
            (closedIntervalCauchyCompletionDecodeBHist
              (closedIntervalCauchyCompletionEncodeBHist R))
            (closedIntervalCauchyCompletionDecodeBHist
              (closedIntervalCauchyCompletionEncodeBHist D))
            (closedIntervalCauchyCompletionDecodeBHist
              (closedIntervalCauchyCompletionEncodeBHist Q))
            (closedIntervalCauchyCompletionDecodeBHist
              (closedIntervalCauchyCompletionEncodeBHist E))
            (closedIntervalCauchyCompletionDecodeBHist
              (closedIntervalCauchyCompletionEncodeBHist H))
            (closedIntervalCauchyCompletionDecodeBHist
              (closedIntervalCauchyCompletionEncodeBHist C))
            (closedIntervalCauchyCompletionDecodeBHist
              (closedIntervalCauchyCompletionEncodeBHist P))
            (closedIntervalCauchyCompletionDecodeBHist
              (closedIntervalCauchyCompletionEncodeBHist N))) =
          some (ClosedIntervalCauchyCompletionUp.mk A B I S R D Q E H C P N)
      rw [ClosedIntervalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode A,
        ClosedIntervalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode B,
        ClosedIntervalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode I,
        ClosedIntervalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode S,
        ClosedIntervalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode R,
        ClosedIntervalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode D,
        ClosedIntervalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode Q,
        ClosedIntervalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode E,
        ClosedIntervalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode H,
        ClosedIntervalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode C,
        ClosedIntervalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode P,
        ClosedIntervalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem ClosedIntervalCauchyCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ClosedIntervalCauchyCompletionUp} :
    closedIntervalCauchyCompletionToEventFlow x =
        closedIntervalCauchyCompletionToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedIntervalCauchyCompletionFromEventFlow
          (closedIntervalCauchyCompletionToEventFlow x) =
        closedIntervalCauchyCompletionFromEventFlow
          (closedIntervalCauchyCompletionToEventFlow y) :=
    congrArg closedIntervalCauchyCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ClosedIntervalCauchyCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ClosedIntervalCauchyCompletionTasteGate_single_carrier_alignment_round_trip y)))

private theorem ClosedIntervalCauchyCompletionTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : ClosedIntervalCauchyCompletionUp,
      closedIntervalCauchyCompletionFields x = closedIntervalCauchyCompletionFields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk A1 B1 I1 S1 R1 D1 Q1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk A2 B2 I2 S2 R2 D2 Q2 E2 H2 C2 P2 N2 =>
          simp only [closedIntervalCauchyCompletionFields] at h
          cases h
          rfl

instance closedIntervalCauchyCompletionBHistCarrier :
    BHistCarrier ClosedIntervalCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedIntervalCauchyCompletionToEventFlow
  fromEventFlow := closedIntervalCauchyCompletionFromEventFlow

instance closedIntervalCauchyCompletionChapterTasteGate :
    ChapterTasteGate ClosedIntervalCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedIntervalCauchyCompletionFromEventFlow
          (closedIntervalCauchyCompletionToEventFlow x) =
        some x
    exact ClosedIntervalCauchyCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ClosedIntervalCauchyCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance closedIntervalCauchyCompletionFieldFaithful :
    FieldFaithful ClosedIntervalCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedIntervalCauchyCompletionFields
  field_faithful :=
    ClosedIntervalCauchyCompletionTasteGate_single_carrier_alignment_fields_faithful

instance closedIntervalCauchyCompletionNontrivial :
    Nontrivial ClosedIntervalCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedIntervalCauchyCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      ClosedIntervalCauchyCompletionUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ClosedIntervalCauchyCompletionTasteGate_single_carrier_alignment :
    (forall h : BHist,
      closedIntervalCauchyCompletionDecodeBHist
          (closedIntervalCauchyCompletionEncodeBHist h) =
        h) ∧
      (forall x : ClosedIntervalCauchyCompletionUp,
        closedIntervalCauchyCompletionFromEventFlow
            (closedIntervalCauchyCompletionToEventFlow x) =
          some x) ∧
        (forall x y : ClosedIntervalCauchyCompletionUp,
          closedIntervalCauchyCompletionToEventFlow x =
              closedIntervalCauchyCompletionToEventFlow y ->
            x = y) ∧
          closedIntervalCauchyCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨ClosedIntervalCauchyCompletionTasteGate_single_carrier_alignment_decode_encode,
      ClosedIntervalCauchyCompletionTasteGate_single_carrier_alignment_round_trip,
      by
        intro x y heq
        exact
          ClosedIntervalCauchyCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
            heq,
      rfl⟩

end BEDC.Derived.ClosedIntervalCauchyCompletionUp
