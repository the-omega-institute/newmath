import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StolzCesaroUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StolzCesaroUp : Type where
  | mk (A B DA DB D T Q E H C P N : BHist) : StolzCesaroUp
  deriving DecidableEq

def StolzCesaroTasteGate_single_carrier_alignment_encodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: StolzCesaroTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: StolzCesaroTasteGate_single_carrier_alignment_encodeBHist h

def StolzCesaroTasteGate_single_carrier_alignment_decodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (StolzCesaroTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (StolzCesaroTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem StolzCesaroTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      StolzCesaroTasteGate_single_carrier_alignment_decodeBHist
        (StolzCesaroTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def StolzCesaroTasteGate_single_carrier_alignment_fields :
    StolzCesaroUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StolzCesaroUp.mk A B DA DB D T Q E H C P N => [A, B, DA, DB, D, T, Q, E, H, C, P, N]

def StolzCesaroTasteGate_single_carrier_alignment_toEventFlow :
    StolzCesaroUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | StolzCesaroUp.mk A B DA DB D T Q E H C P N =>
      [[BMark.b1, BMark.b1, BMark.b0, BMark.b0],
        StolzCesaroTasteGate_single_carrier_alignment_encodeBHist A,
        StolzCesaroTasteGate_single_carrier_alignment_encodeBHist B,
        StolzCesaroTasteGate_single_carrier_alignment_encodeBHist DA,
        StolzCesaroTasteGate_single_carrier_alignment_encodeBHist DB,
        StolzCesaroTasteGate_single_carrier_alignment_encodeBHist D,
        StolzCesaroTasteGate_single_carrier_alignment_encodeBHist T,
        StolzCesaroTasteGate_single_carrier_alignment_encodeBHist Q,
        StolzCesaroTasteGate_single_carrier_alignment_encodeBHist E,
        StolzCesaroTasteGate_single_carrier_alignment_encodeBHist H,
        StolzCesaroTasteGate_single_carrier_alignment_encodeBHist C,
        StolzCesaroTasteGate_single_carrier_alignment_encodeBHist P,
        StolzCesaroTasteGate_single_carrier_alignment_encodeBHist N]

private def StolzCesaroTasteGate_single_carrier_alignment_eventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      StolzCesaroTasteGate_single_carrier_alignment_eventAtDefault index rest

def StolzCesaroTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option StolzCesaroUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (StolzCesaroUp.mk
      (StolzCesaroTasteGate_single_carrier_alignment_decodeBHist
        (StolzCesaroTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (StolzCesaroTasteGate_single_carrier_alignment_decodeBHist
        (StolzCesaroTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (StolzCesaroTasteGate_single_carrier_alignment_decodeBHist
        (StolzCesaroTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (StolzCesaroTasteGate_single_carrier_alignment_decodeBHist
        (StolzCesaroTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (StolzCesaroTasteGate_single_carrier_alignment_decodeBHist
        (StolzCesaroTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (StolzCesaroTasteGate_single_carrier_alignment_decodeBHist
        (StolzCesaroTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (StolzCesaroTasteGate_single_carrier_alignment_decodeBHist
        (StolzCesaroTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (StolzCesaroTasteGate_single_carrier_alignment_decodeBHist
        (StolzCesaroTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (StolzCesaroTasteGate_single_carrier_alignment_decodeBHist
        (StolzCesaroTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (StolzCesaroTasteGate_single_carrier_alignment_decodeBHist
        (StolzCesaroTasteGate_single_carrier_alignment_eventAtDefault 10 ef))
      (StolzCesaroTasteGate_single_carrier_alignment_decodeBHist
        (StolzCesaroTasteGate_single_carrier_alignment_eventAtDefault 11 ef))
      (StolzCesaroTasteGate_single_carrier_alignment_decodeBHist
        (StolzCesaroTasteGate_single_carrier_alignment_eventAtDefault 12 ef)))

private theorem StolzCesaroTasteGate_single_carrier_alignment_round_trip :
    forall x : StolzCesaroUp,
      StolzCesaroTasteGate_single_carrier_alignment_fromEventFlow
        (StolzCesaroTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B DA DB D T Q E H C P N =>
      change
        some
          (StolzCesaroUp.mk
            (StolzCesaroTasteGate_single_carrier_alignment_decodeBHist
              (StolzCesaroTasteGate_single_carrier_alignment_encodeBHist A))
            (StolzCesaroTasteGate_single_carrier_alignment_decodeBHist
              (StolzCesaroTasteGate_single_carrier_alignment_encodeBHist B))
            (StolzCesaroTasteGate_single_carrier_alignment_decodeBHist
              (StolzCesaroTasteGate_single_carrier_alignment_encodeBHist DA))
            (StolzCesaroTasteGate_single_carrier_alignment_decodeBHist
              (StolzCesaroTasteGate_single_carrier_alignment_encodeBHist DB))
            (StolzCesaroTasteGate_single_carrier_alignment_decodeBHist
              (StolzCesaroTasteGate_single_carrier_alignment_encodeBHist D))
            (StolzCesaroTasteGate_single_carrier_alignment_decodeBHist
              (StolzCesaroTasteGate_single_carrier_alignment_encodeBHist T))
            (StolzCesaroTasteGate_single_carrier_alignment_decodeBHist
              (StolzCesaroTasteGate_single_carrier_alignment_encodeBHist Q))
            (StolzCesaroTasteGate_single_carrier_alignment_decodeBHist
              (StolzCesaroTasteGate_single_carrier_alignment_encodeBHist E))
            (StolzCesaroTasteGate_single_carrier_alignment_decodeBHist
              (StolzCesaroTasteGate_single_carrier_alignment_encodeBHist H))
            (StolzCesaroTasteGate_single_carrier_alignment_decodeBHist
              (StolzCesaroTasteGate_single_carrier_alignment_encodeBHist C))
            (StolzCesaroTasteGate_single_carrier_alignment_decodeBHist
              (StolzCesaroTasteGate_single_carrier_alignment_encodeBHist P))
            (StolzCesaroTasteGate_single_carrier_alignment_decodeBHist
              (StolzCesaroTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (StolzCesaroUp.mk A B DA DB D T Q E H C P N)
      rw [StolzCesaroTasteGate_single_carrier_alignment_decode A,
        StolzCesaroTasteGate_single_carrier_alignment_decode B,
        StolzCesaroTasteGate_single_carrier_alignment_decode DA,
        StolzCesaroTasteGate_single_carrier_alignment_decode DB,
        StolzCesaroTasteGate_single_carrier_alignment_decode D,
        StolzCesaroTasteGate_single_carrier_alignment_decode T,
        StolzCesaroTasteGate_single_carrier_alignment_decode Q,
        StolzCesaroTasteGate_single_carrier_alignment_decode E,
        StolzCesaroTasteGate_single_carrier_alignment_decode H,
        StolzCesaroTasteGate_single_carrier_alignment_decode C,
        StolzCesaroTasteGate_single_carrier_alignment_decode P,
        StolzCesaroTasteGate_single_carrier_alignment_decode N]

private theorem StolzCesaroTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : StolzCesaroUp} :
    StolzCesaroTasteGate_single_carrier_alignment_toEventFlow x =
        StolzCesaroTasteGate_single_carrier_alignment_toEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      StolzCesaroTasteGate_single_carrier_alignment_fromEventFlow
          (StolzCesaroTasteGate_single_carrier_alignment_toEventFlow x) =
        StolzCesaroTasteGate_single_carrier_alignment_fromEventFlow
          (StolzCesaroTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg StolzCesaroTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (StolzCesaroTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (StolzCesaroTasteGate_single_carrier_alignment_round_trip y)))

private theorem StolzCesaroTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : StolzCesaroUp,
      StolzCesaroTasteGate_single_carrier_alignment_fields x =
          StolzCesaroTasteGate_single_carrier_alignment_fields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 B1 DA1 DB1 D1 T1 Q1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk A2 B2 DA2 DB2 D2 T2 Q2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance stolzCesaroBHistCarrier : BHistCarrier StolzCesaroUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := StolzCesaroTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := StolzCesaroTasteGate_single_carrier_alignment_fromEventFlow

instance stolzCesaroChapterTasteGate : ChapterTasteGate StolzCesaroUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      StolzCesaroTasteGate_single_carrier_alignment_fromEventFlow
        (StolzCesaroTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact StolzCesaroTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (StolzCesaroTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance stolzCesaroFieldFaithful : FieldFaithful StolzCesaroUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := StolzCesaroTasteGate_single_carrier_alignment_fields
  field_faithful := StolzCesaroTasteGate_single_carrier_alignment_fields_faithful

instance stolzCesaroNontrivial : Nontrivial StolzCesaroUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨StolzCesaroUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      StolzCesaroUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate StolzCesaroUp :=
  -- BEDC touchpoint anchor: BHist BMark
  stolzCesaroChapterTasteGate

theorem StolzCesaroTasteGate_single_carrier_alignment :
    (forall h : BHist,
      StolzCesaroTasteGate_single_carrier_alignment_decodeBHist
        (StolzCesaroTasteGate_single_carrier_alignment_encodeBHist h) = h) ∧
      StolzCesaroTasteGate_single_carrier_alignment_fields
        (StolzCesaroUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
      StolzCesaroTasteGate_single_carrier_alignment_toEventFlow
        (StolzCesaroUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [[BMark.b1, BMark.b1, BMark.b0, BMark.b0], [], [], [], [], [], [], [], [], [],
          [], [], []] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact StolzCesaroTasteGate_single_carrier_alignment_decode
  · constructor
    · rfl
    · rfl

end BEDC.Derived.StolzCesaroUp
