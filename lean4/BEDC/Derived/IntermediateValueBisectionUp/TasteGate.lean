import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IntermediateValueBisectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive IntermediateValueBisectionUp : Type where
  | mk (J R D S W G E H C P N : BHist) : IntermediateValueBisectionUp
  deriving DecidableEq

def IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist :
    BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 ::
      IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 ::
      IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist h

def IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem IntermediateValueBisectionTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist
        (IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def IntermediateValueBisectionTasteGate_single_carrier_alignment_fields :
    IntermediateValueBisectionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | IntermediateValueBisectionUp.mk J R D S W G E H C P N =>
      [J, R, D, S, W, G, E, H, C, P, N]

def IntermediateValueBisectionTasteGate_single_carrier_alignment_toEventFlow :
    IntermediateValueBisectionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | IntermediateValueBisectionUp.mk J R D S W G E H C P N =>
      [[BMark.b1, BMark.b0, BMark.b1, BMark.b0],
        IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist J,
        IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist R,
        IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist D,
        IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist S,
        IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist W,
        IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist G,
        IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist E,
        IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist H,
        IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist C,
        IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist P,
        IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist N]

private def IntermediateValueBisectionTasteGate_single_carrier_alignment_eventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      IntermediateValueBisectionTasteGate_single_carrier_alignment_eventAtDefault index rest

def IntermediateValueBisectionTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option IntermediateValueBisectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (IntermediateValueBisectionUp.mk
      (IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist
        (IntermediateValueBisectionTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist
        (IntermediateValueBisectionTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist
        (IntermediateValueBisectionTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist
        (IntermediateValueBisectionTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist
        (IntermediateValueBisectionTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist
        (IntermediateValueBisectionTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist
        (IntermediateValueBisectionTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist
        (IntermediateValueBisectionTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist
        (IntermediateValueBisectionTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist
        (IntermediateValueBisectionTasteGate_single_carrier_alignment_eventAtDefault 10 ef))
      (IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist
        (IntermediateValueBisectionTasteGate_single_carrier_alignment_eventAtDefault 11 ef)))

private theorem IntermediateValueBisectionTasteGate_single_carrier_alignment_round_trip :
    forall x : IntermediateValueBisectionUp,
      IntermediateValueBisectionTasteGate_single_carrier_alignment_fromEventFlow
        (IntermediateValueBisectionTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk J R D S W G E H C P N =>
      change
        some
          (IntermediateValueBisectionUp.mk
            (IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist
              (IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist J))
            (IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist
              (IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist R))
            (IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist
              (IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist D))
            (IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist
              (IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist S))
            (IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist
              (IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist W))
            (IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist
              (IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist G))
            (IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist
              (IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist E))
            (IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist
              (IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist H))
            (IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist
              (IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist C))
            (IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist
              (IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist P))
            (IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist
              (IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (IntermediateValueBisectionUp.mk J R D S W G E H C P N)
      rw [IntermediateValueBisectionTasteGate_single_carrier_alignment_decode J,
        IntermediateValueBisectionTasteGate_single_carrier_alignment_decode R,
        IntermediateValueBisectionTasteGate_single_carrier_alignment_decode D,
        IntermediateValueBisectionTasteGate_single_carrier_alignment_decode S,
        IntermediateValueBisectionTasteGate_single_carrier_alignment_decode W,
        IntermediateValueBisectionTasteGate_single_carrier_alignment_decode G,
        IntermediateValueBisectionTasteGate_single_carrier_alignment_decode E,
        IntermediateValueBisectionTasteGate_single_carrier_alignment_decode H,
        IntermediateValueBisectionTasteGate_single_carrier_alignment_decode C,
        IntermediateValueBisectionTasteGate_single_carrier_alignment_decode P,
        IntermediateValueBisectionTasteGate_single_carrier_alignment_decode N]

private theorem IntermediateValueBisectionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : IntermediateValueBisectionUp} :
    IntermediateValueBisectionTasteGate_single_carrier_alignment_toEventFlow x =
        IntermediateValueBisectionTasteGate_single_carrier_alignment_toEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      IntermediateValueBisectionTasteGate_single_carrier_alignment_fromEventFlow
          (IntermediateValueBisectionTasteGate_single_carrier_alignment_toEventFlow x) =
        IntermediateValueBisectionTasteGate_single_carrier_alignment_fromEventFlow
          (IntermediateValueBisectionTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg IntermediateValueBisectionTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (IntermediateValueBisectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (IntermediateValueBisectionTasteGate_single_carrier_alignment_round_trip y)))

private theorem IntermediateValueBisectionTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : IntermediateValueBisectionUp,
      IntermediateValueBisectionTasteGate_single_carrier_alignment_fields x =
          IntermediateValueBisectionTasteGate_single_carrier_alignment_fields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk J1 R1 D1 S1 W1 G1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk J2 R2 D2 S2 W2 G2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance intermediateValueBisectionBHistCarrier :
    BHistCarrier IntermediateValueBisectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := IntermediateValueBisectionTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := IntermediateValueBisectionTasteGate_single_carrier_alignment_fromEventFlow

instance intermediateValueBisectionChapterTasteGate :
    ChapterTasteGate IntermediateValueBisectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      IntermediateValueBisectionTasteGate_single_carrier_alignment_fromEventFlow
        (IntermediateValueBisectionTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact IntermediateValueBisectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (IntermediateValueBisectionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance intermediateValueBisectionFieldFaithful :
    FieldFaithful IntermediateValueBisectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := IntermediateValueBisectionTasteGate_single_carrier_alignment_fields
  field_faithful := IntermediateValueBisectionTasteGate_single_carrier_alignment_fields_faithful

instance intermediateValueBisectionNontrivial : Nontrivial IntermediateValueBisectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨IntermediateValueBisectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      IntermediateValueBisectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate IntermediateValueBisectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  intermediateValueBisectionChapterTasteGate

theorem IntermediateValueBisectionTasteGate_single_carrier_alignment :
    (forall h : BHist,
      IntermediateValueBisectionTasteGate_single_carrier_alignment_decodeBHist
        (IntermediateValueBisectionTasteGate_single_carrier_alignment_encodeBHist h) = h) ∧
      IntermediateValueBisectionTasteGate_single_carrier_alignment_fields
        (IntermediateValueBisectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
      IntermediateValueBisectionTasteGate_single_carrier_alignment_toEventFlow
        (IntermediateValueBisectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [[BMark.b1, BMark.b0, BMark.b1, BMark.b0], [], [], [], [], [], [], [], [], [],
          [], []] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact IntermediateValueBisectionTasteGate_single_carrier_alignment_decode
  · constructor
    · rfl
    · rfl

end BEDC.Derived.IntermediateValueBisectionUp
