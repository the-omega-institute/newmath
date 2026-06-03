import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NestedClosedBallUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NestedClosedBallUp : Type where
  | mk (M K F S R D E H C P N : BHist) : NestedClosedBallUp
  deriving DecidableEq

def NestedClosedBallTasteGate_single_carrier_alignment_encodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: NestedClosedBallTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: NestedClosedBallTasteGate_single_carrier_alignment_encodeBHist h

def NestedClosedBallTasteGate_single_carrier_alignment_decodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (NestedClosedBallTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (NestedClosedBallTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem NestedClosedBallTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      NestedClosedBallTasteGate_single_carrier_alignment_decodeBHist
        (NestedClosedBallTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def NestedClosedBallTasteGate_single_carrier_alignment_fields :
    NestedClosedBallUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NestedClosedBallUp.mk M K F S R D E H C P N => [M, K, F, S, R, D, E, H, C, P, N]

def NestedClosedBallTasteGate_single_carrier_alignment_toEventFlow :
    NestedClosedBallUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (NestedClosedBallTasteGate_single_carrier_alignment_fields x).map
        NestedClosedBallTasteGate_single_carrier_alignment_encodeBHist

private def NestedClosedBallTasteGate_single_carrier_alignment_eventAt :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      NestedClosedBallTasteGate_single_carrier_alignment_eventAt index rest

def NestedClosedBallTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow -> Option NestedClosedBallUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (NestedClosedBallUp.mk
          (NestedClosedBallTasteGate_single_carrier_alignment_decodeBHist
            (NestedClosedBallTasteGate_single_carrier_alignment_eventAt 0 flow))
          (NestedClosedBallTasteGate_single_carrier_alignment_decodeBHist
            (NestedClosedBallTasteGate_single_carrier_alignment_eventAt 1 flow))
          (NestedClosedBallTasteGate_single_carrier_alignment_decodeBHist
            (NestedClosedBallTasteGate_single_carrier_alignment_eventAt 2 flow))
          (NestedClosedBallTasteGate_single_carrier_alignment_decodeBHist
            (NestedClosedBallTasteGate_single_carrier_alignment_eventAt 3 flow))
          (NestedClosedBallTasteGate_single_carrier_alignment_decodeBHist
            (NestedClosedBallTasteGate_single_carrier_alignment_eventAt 4 flow))
          (NestedClosedBallTasteGate_single_carrier_alignment_decodeBHist
            (NestedClosedBallTasteGate_single_carrier_alignment_eventAt 5 flow))
          (NestedClosedBallTasteGate_single_carrier_alignment_decodeBHist
            (NestedClosedBallTasteGate_single_carrier_alignment_eventAt 6 flow))
          (NestedClosedBallTasteGate_single_carrier_alignment_decodeBHist
            (NestedClosedBallTasteGate_single_carrier_alignment_eventAt 7 flow))
          (NestedClosedBallTasteGate_single_carrier_alignment_decodeBHist
            (NestedClosedBallTasteGate_single_carrier_alignment_eventAt 8 flow))
          (NestedClosedBallTasteGate_single_carrier_alignment_decodeBHist
            (NestedClosedBallTasteGate_single_carrier_alignment_eventAt 9 flow))
          (NestedClosedBallTasteGate_single_carrier_alignment_decodeBHist
            (NestedClosedBallTasteGate_single_carrier_alignment_eventAt 10 flow)))

private theorem NestedClosedBallTasteGate_single_carrier_alignment_round_trip :
    forall x : NestedClosedBallUp,
      NestedClosedBallTasteGate_single_carrier_alignment_fromEventFlow
        (NestedClosedBallTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M K F S R D E H C P N =>
      change
        some
          (NestedClosedBallUp.mk
            (NestedClosedBallTasteGate_single_carrier_alignment_decodeBHist
              (NestedClosedBallTasteGate_single_carrier_alignment_encodeBHist M))
            (NestedClosedBallTasteGate_single_carrier_alignment_decodeBHist
              (NestedClosedBallTasteGate_single_carrier_alignment_encodeBHist K))
            (NestedClosedBallTasteGate_single_carrier_alignment_decodeBHist
              (NestedClosedBallTasteGate_single_carrier_alignment_encodeBHist F))
            (NestedClosedBallTasteGate_single_carrier_alignment_decodeBHist
              (NestedClosedBallTasteGate_single_carrier_alignment_encodeBHist S))
            (NestedClosedBallTasteGate_single_carrier_alignment_decodeBHist
              (NestedClosedBallTasteGate_single_carrier_alignment_encodeBHist R))
            (NestedClosedBallTasteGate_single_carrier_alignment_decodeBHist
              (NestedClosedBallTasteGate_single_carrier_alignment_encodeBHist D))
            (NestedClosedBallTasteGate_single_carrier_alignment_decodeBHist
              (NestedClosedBallTasteGate_single_carrier_alignment_encodeBHist E))
            (NestedClosedBallTasteGate_single_carrier_alignment_decodeBHist
              (NestedClosedBallTasteGate_single_carrier_alignment_encodeBHist H))
            (NestedClosedBallTasteGate_single_carrier_alignment_decodeBHist
              (NestedClosedBallTasteGate_single_carrier_alignment_encodeBHist C))
            (NestedClosedBallTasteGate_single_carrier_alignment_decodeBHist
              (NestedClosedBallTasteGate_single_carrier_alignment_encodeBHist P))
            (NestedClosedBallTasteGate_single_carrier_alignment_decodeBHist
              (NestedClosedBallTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (NestedClosedBallUp.mk M K F S R D E H C P N)
      rw [NestedClosedBallTasteGate_single_carrier_alignment_decode M,
        NestedClosedBallTasteGate_single_carrier_alignment_decode K,
        NestedClosedBallTasteGate_single_carrier_alignment_decode F,
        NestedClosedBallTasteGate_single_carrier_alignment_decode S,
        NestedClosedBallTasteGate_single_carrier_alignment_decode R,
        NestedClosedBallTasteGate_single_carrier_alignment_decode D,
        NestedClosedBallTasteGate_single_carrier_alignment_decode E,
        NestedClosedBallTasteGate_single_carrier_alignment_decode H,
        NestedClosedBallTasteGate_single_carrier_alignment_decode C,
        NestedClosedBallTasteGate_single_carrier_alignment_decode P,
        NestedClosedBallTasteGate_single_carrier_alignment_decode N]

private theorem NestedClosedBallTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : NestedClosedBallUp} :
    NestedClosedBallTasteGate_single_carrier_alignment_toEventFlow x =
      NestedClosedBallTasteGate_single_carrier_alignment_toEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      NestedClosedBallTasteGate_single_carrier_alignment_fromEventFlow
          (NestedClosedBallTasteGate_single_carrier_alignment_toEventFlow x) =
        NestedClosedBallTasteGate_single_carrier_alignment_fromEventFlow
          (NestedClosedBallTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg NestedClosedBallTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (NestedClosedBallTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (NestedClosedBallTasteGate_single_carrier_alignment_round_trip y)))

private theorem NestedClosedBallTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : NestedClosedBallUp,
      NestedClosedBallTasteGate_single_carrier_alignment_fields x =
        NestedClosedBallTasteGate_single_carrier_alignment_fields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 K1 F1 S1 R1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 K2 F2 S2 R2 D2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance nestedClosedBallBHistCarrier : BHistCarrier NestedClosedBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := NestedClosedBallTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := NestedClosedBallTasteGate_single_carrier_alignment_fromEventFlow

instance nestedClosedBallChapterTasteGate : ChapterTasteGate NestedClosedBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      NestedClosedBallTasteGate_single_carrier_alignment_fromEventFlow
        (NestedClosedBallTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact NestedClosedBallTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (NestedClosedBallTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance nestedClosedBallFieldFaithful : FieldFaithful NestedClosedBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := NestedClosedBallTasteGate_single_carrier_alignment_fields
  field_faithful := NestedClosedBallTasteGate_single_carrier_alignment_fields_faithful

instance nestedClosedBallNontrivial : Nontrivial NestedClosedBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NestedClosedBallUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      NestedClosedBallUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem NestedClosedBallTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate NestedClosedBallUp) /\
      (forall x : NestedClosedBallUp,
        exists e : EventFlow, BHistCarrier.fromEventFlow e = some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨nestedClosedBallChapterTasteGate⟩
  · intro x
    exact
      ⟨NestedClosedBallTasteGate_single_carrier_alignment_toEventFlow x,
        ChapterTasteGate.round_trip x⟩

end BEDC.Derived.NestedClosedBallUp.TasteGate
