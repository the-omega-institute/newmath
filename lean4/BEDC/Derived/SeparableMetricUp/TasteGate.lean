import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SeparableMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SeparableMetricUp : Type where
  | mk (M A W T R E H C P N : BHist) : SeparableMetricUp
  deriving DecidableEq

def SeparableMetricTasteGate_single_carrier_alignment_encodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: SeparableMetricTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: SeparableMetricTasteGate_single_carrier_alignment_encodeBHist h

def SeparableMetricTasteGate_single_carrier_alignment_decodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (SeparableMetricTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (SeparableMetricTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem SeparableMetricTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      SeparableMetricTasteGate_single_carrier_alignment_decodeBHist
        (SeparableMetricTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def SeparableMetricTasteGate_single_carrier_alignment_fields :
    SeparableMetricUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SeparableMetricUp.mk M A W T R E H C P N => [M, A, W, T, R, E, H, C, P, N]

def SeparableMetricTasteGate_single_carrier_alignment_toEventFlow :
    SeparableMetricUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SeparableMetricUp.mk M A W T R E H C P N =>
      [[BMark.b0, BMark.b1, BMark.b1, BMark.b0],
        SeparableMetricTasteGate_single_carrier_alignment_encodeBHist M,
        SeparableMetricTasteGate_single_carrier_alignment_encodeBHist A,
        SeparableMetricTasteGate_single_carrier_alignment_encodeBHist W,
        SeparableMetricTasteGate_single_carrier_alignment_encodeBHist T,
        SeparableMetricTasteGate_single_carrier_alignment_encodeBHist R,
        SeparableMetricTasteGate_single_carrier_alignment_encodeBHist E,
        SeparableMetricTasteGate_single_carrier_alignment_encodeBHist H,
        SeparableMetricTasteGate_single_carrier_alignment_encodeBHist C,
        SeparableMetricTasteGate_single_carrier_alignment_encodeBHist P,
        SeparableMetricTasteGate_single_carrier_alignment_encodeBHist N]

private def SeparableMetricTasteGate_single_carrier_alignment_eventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      SeparableMetricTasteGate_single_carrier_alignment_eventAtDefault index rest

def SeparableMetricTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option SeparableMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SeparableMetricUp.mk
      (SeparableMetricTasteGate_single_carrier_alignment_decodeBHist
        (SeparableMetricTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (SeparableMetricTasteGate_single_carrier_alignment_decodeBHist
        (SeparableMetricTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (SeparableMetricTasteGate_single_carrier_alignment_decodeBHist
        (SeparableMetricTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (SeparableMetricTasteGate_single_carrier_alignment_decodeBHist
        (SeparableMetricTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (SeparableMetricTasteGate_single_carrier_alignment_decodeBHist
        (SeparableMetricTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (SeparableMetricTasteGate_single_carrier_alignment_decodeBHist
        (SeparableMetricTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (SeparableMetricTasteGate_single_carrier_alignment_decodeBHist
        (SeparableMetricTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (SeparableMetricTasteGate_single_carrier_alignment_decodeBHist
        (SeparableMetricTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (SeparableMetricTasteGate_single_carrier_alignment_decodeBHist
        (SeparableMetricTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (SeparableMetricTasteGate_single_carrier_alignment_decodeBHist
        (SeparableMetricTasteGate_single_carrier_alignment_eventAtDefault 10 ef)))

private theorem SeparableMetricTasteGate_single_carrier_alignment_round_trip :
    forall x : SeparableMetricUp,
      SeparableMetricTasteGate_single_carrier_alignment_fromEventFlow
        (SeparableMetricTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M A W T R E H C P N =>
      change
        some
          (SeparableMetricUp.mk
            (SeparableMetricTasteGate_single_carrier_alignment_decodeBHist
              (SeparableMetricTasteGate_single_carrier_alignment_encodeBHist M))
            (SeparableMetricTasteGate_single_carrier_alignment_decodeBHist
              (SeparableMetricTasteGate_single_carrier_alignment_encodeBHist A))
            (SeparableMetricTasteGate_single_carrier_alignment_decodeBHist
              (SeparableMetricTasteGate_single_carrier_alignment_encodeBHist W))
            (SeparableMetricTasteGate_single_carrier_alignment_decodeBHist
              (SeparableMetricTasteGate_single_carrier_alignment_encodeBHist T))
            (SeparableMetricTasteGate_single_carrier_alignment_decodeBHist
              (SeparableMetricTasteGate_single_carrier_alignment_encodeBHist R))
            (SeparableMetricTasteGate_single_carrier_alignment_decodeBHist
              (SeparableMetricTasteGate_single_carrier_alignment_encodeBHist E))
            (SeparableMetricTasteGate_single_carrier_alignment_decodeBHist
              (SeparableMetricTasteGate_single_carrier_alignment_encodeBHist H))
            (SeparableMetricTasteGate_single_carrier_alignment_decodeBHist
              (SeparableMetricTasteGate_single_carrier_alignment_encodeBHist C))
            (SeparableMetricTasteGate_single_carrier_alignment_decodeBHist
              (SeparableMetricTasteGate_single_carrier_alignment_encodeBHist P))
            (SeparableMetricTasteGate_single_carrier_alignment_decodeBHist
              (SeparableMetricTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (SeparableMetricUp.mk M A W T R E H C P N)
      rw [SeparableMetricTasteGate_single_carrier_alignment_decode M,
        SeparableMetricTasteGate_single_carrier_alignment_decode A,
        SeparableMetricTasteGate_single_carrier_alignment_decode W,
        SeparableMetricTasteGate_single_carrier_alignment_decode T,
        SeparableMetricTasteGate_single_carrier_alignment_decode R,
        SeparableMetricTasteGate_single_carrier_alignment_decode E,
        SeparableMetricTasteGate_single_carrier_alignment_decode H,
        SeparableMetricTasteGate_single_carrier_alignment_decode C,
        SeparableMetricTasteGate_single_carrier_alignment_decode P,
        SeparableMetricTasteGate_single_carrier_alignment_decode N]

private theorem SeparableMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SeparableMetricUp} :
    SeparableMetricTasteGate_single_carrier_alignment_toEventFlow x =
        SeparableMetricTasteGate_single_carrier_alignment_toEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      SeparableMetricTasteGate_single_carrier_alignment_fromEventFlow
          (SeparableMetricTasteGate_single_carrier_alignment_toEventFlow x) =
        SeparableMetricTasteGate_single_carrier_alignment_fromEventFlow
          (SeparableMetricTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg SeparableMetricTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SeparableMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SeparableMetricTasteGate_single_carrier_alignment_round_trip y)))

private theorem SeparableMetricTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : SeparableMetricUp,
      SeparableMetricTasteGate_single_carrier_alignment_fields x =
          SeparableMetricTasteGate_single_carrier_alignment_fields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 A1 W1 T1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 A2 W2 T2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance separableMetricBHistCarrier : BHistCarrier SeparableMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := SeparableMetricTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := SeparableMetricTasteGate_single_carrier_alignment_fromEventFlow

instance separableMetricChapterTasteGate : ChapterTasteGate SeparableMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      SeparableMetricTasteGate_single_carrier_alignment_fromEventFlow
        (SeparableMetricTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact SeparableMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SeparableMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance separableMetricFieldFaithful : FieldFaithful SeparableMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := SeparableMetricTasteGate_single_carrier_alignment_fields
  field_faithful := SeparableMetricTasteGate_single_carrier_alignment_fields_faithful

instance separableMetricNontrivial : Nontrivial SeparableMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SeparableMetricUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SeparableMetricUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SeparableMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  separableMetricChapterTasteGate

theorem SeparableMetricTasteGate_single_carrier_alignment :
    (forall h : BHist,
      SeparableMetricTasteGate_single_carrier_alignment_decodeBHist
        (SeparableMetricTasteGate_single_carrier_alignment_encodeBHist h) = h) ∧
      SeparableMetricTasteGate_single_carrier_alignment_fields
        (SeparableMetricUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
      SeparableMetricTasteGate_single_carrier_alignment_toEventFlow
        (SeparableMetricUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [[BMark.b0, BMark.b1, BMark.b1, BMark.b0], [], [], [], [], [], [], [], [],
          [], []] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact SeparableMetricTasteGate_single_carrier_alignment_decode
  · constructor
    · rfl
    · rfl

end BEDC.Derived.SeparableMetricUp
