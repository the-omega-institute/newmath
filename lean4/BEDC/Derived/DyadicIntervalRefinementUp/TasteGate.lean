import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicIntervalRefinementUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicIntervalRefinementUp : Type where
  | mk (I J0 J1 E R S Q H C P N : BHist) : DyadicIntervalRefinementUp
  deriving DecidableEq

def dyadicIntervalRefinementEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicIntervalRefinementEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicIntervalRefinementEncodeBHist h

def dyadicIntervalRefinementDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicIntervalRefinementDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicIntervalRefinementDecodeBHist tail)

private theorem dyadicIntervalRefinement_decode_encode_bhist :
    forall h : BHist,
      dyadicIntervalRefinementDecodeBHist (dyadicIntervalRefinementEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicIntervalRefinementFields : DyadicIntervalRefinementUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicIntervalRefinementUp.mk I J0 J1 E R S Q H C P N =>
      [I, J0, J1, E, R, S, Q, H, C, P, N]

def dyadicIntervalRefinementToEventFlow : DyadicIntervalRefinementUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (dyadicIntervalRefinementFields x).map dyadicIntervalRefinementEncodeBHist

private def dyadicIntervalRefinementEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicIntervalRefinementEventAt index rest

def dyadicIntervalRefinementFromEventFlow
    (ef : EventFlow) : Option DyadicIntervalRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicIntervalRefinementUp.mk
      (dyadicIntervalRefinementDecodeBHist (dyadicIntervalRefinementEventAt 0 ef))
      (dyadicIntervalRefinementDecodeBHist (dyadicIntervalRefinementEventAt 1 ef))
      (dyadicIntervalRefinementDecodeBHist (dyadicIntervalRefinementEventAt 2 ef))
      (dyadicIntervalRefinementDecodeBHist (dyadicIntervalRefinementEventAt 3 ef))
      (dyadicIntervalRefinementDecodeBHist (dyadicIntervalRefinementEventAt 4 ef))
      (dyadicIntervalRefinementDecodeBHist (dyadicIntervalRefinementEventAt 5 ef))
      (dyadicIntervalRefinementDecodeBHist (dyadicIntervalRefinementEventAt 6 ef))
      (dyadicIntervalRefinementDecodeBHist (dyadicIntervalRefinementEventAt 7 ef))
      (dyadicIntervalRefinementDecodeBHist (dyadicIntervalRefinementEventAt 8 ef))
      (dyadicIntervalRefinementDecodeBHist (dyadicIntervalRefinementEventAt 9 ef))
      (dyadicIntervalRefinementDecodeBHist (dyadicIntervalRefinementEventAt 10 ef)))

private theorem dyadicIntervalRefinement_round_trip
    (x : DyadicIntervalRefinementUp) :
    dyadicIntervalRefinementFromEventFlow (dyadicIntervalRefinementToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I J0 J1 E R S Q H C P N =>
      change
        some
          (DyadicIntervalRefinementUp.mk
            (dyadicIntervalRefinementDecodeBHist
              (dyadicIntervalRefinementEncodeBHist I))
            (dyadicIntervalRefinementDecodeBHist
              (dyadicIntervalRefinementEncodeBHist J0))
            (dyadicIntervalRefinementDecodeBHist
              (dyadicIntervalRefinementEncodeBHist J1))
            (dyadicIntervalRefinementDecodeBHist
              (dyadicIntervalRefinementEncodeBHist E))
            (dyadicIntervalRefinementDecodeBHist
              (dyadicIntervalRefinementEncodeBHist R))
            (dyadicIntervalRefinementDecodeBHist
              (dyadicIntervalRefinementEncodeBHist S))
            (dyadicIntervalRefinementDecodeBHist
              (dyadicIntervalRefinementEncodeBHist Q))
            (dyadicIntervalRefinementDecodeBHist
              (dyadicIntervalRefinementEncodeBHist H))
            (dyadicIntervalRefinementDecodeBHist
              (dyadicIntervalRefinementEncodeBHist C))
            (dyadicIntervalRefinementDecodeBHist
              (dyadicIntervalRefinementEncodeBHist P))
            (dyadicIntervalRefinementDecodeBHist
              (dyadicIntervalRefinementEncodeBHist N))) =
          some (DyadicIntervalRefinementUp.mk I J0 J1 E R S Q H C P N)
      rw [dyadicIntervalRefinement_decode_encode_bhist I,
        dyadicIntervalRefinement_decode_encode_bhist J0,
        dyadicIntervalRefinement_decode_encode_bhist J1,
        dyadicIntervalRefinement_decode_encode_bhist E,
        dyadicIntervalRefinement_decode_encode_bhist R,
        dyadicIntervalRefinement_decode_encode_bhist S,
        dyadicIntervalRefinement_decode_encode_bhist Q,
        dyadicIntervalRefinement_decode_encode_bhist H,
        dyadicIntervalRefinement_decode_encode_bhist C,
        dyadicIntervalRefinement_decode_encode_bhist P,
        dyadicIntervalRefinement_decode_encode_bhist N]

private theorem dyadicIntervalRefinementToEventFlow_injective
    {x y : DyadicIntervalRefinementUp} :
    dyadicIntervalRefinementToEventFlow x = dyadicIntervalRefinementToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicIntervalRefinementFromEventFlow (dyadicIntervalRefinementToEventFlow x) =
        dyadicIntervalRefinementFromEventFlow (dyadicIntervalRefinementToEventFlow y) :=
    congrArg dyadicIntervalRefinementFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicIntervalRefinement_round_trip x).symm
      (Eq.trans hread (dyadicIntervalRefinement_round_trip y)))

private theorem dyadicIntervalRefinement_fields_faithful :
    forall x y : DyadicIntervalRefinementUp,
      dyadicIntervalRefinementFields x = dyadicIntervalRefinementFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 J01 J11 E1 R1 S1 Q1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 J02 J12 E2 R2 S2 Q2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance dyadicIntervalRefinementBHistCarrier :
    BHistCarrier DyadicIntervalRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicIntervalRefinementToEventFlow
  fromEventFlow := dyadicIntervalRefinementFromEventFlow

instance dyadicIntervalRefinementChapterTasteGate :
    ChapterTasteGate DyadicIntervalRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dyadicIntervalRefinementFromEventFlow (dyadicIntervalRefinementToEventFlow x) =
        some x
    exact dyadicIntervalRefinement_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicIntervalRefinementToEventFlow_injective heq)

instance dyadicIntervalRefinementFieldFaithful :
    FieldFaithful DyadicIntervalRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicIntervalRefinementFields
  field_faithful := dyadicIntervalRefinement_fields_faithful

instance dyadicIntervalRefinementNontrivial :
    BEDC.Meta.TasteGate.Nontrivial DyadicIntervalRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicIntervalRefinementUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      DyadicIntervalRefinementUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem DyadicIntervalRefinementTasteGate_single_carrier_alignment :
    (forall h : BHist,
        dyadicIntervalRefinementDecodeBHist (dyadicIntervalRefinementEncodeBHist h) = h) ∧
      (forall x : DyadicIntervalRefinementUp,
        dyadicIntervalRefinementFromEventFlow (dyadicIntervalRefinementToEventFlow x) =
          some x) ∧
      (forall x y : DyadicIntervalRefinementUp,
        dyadicIntervalRefinementToEventFlow x = dyadicIntervalRefinementToEventFlow y ->
          x = y) ∧
      dyadicIntervalRefinementEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨dyadicIntervalRefinement_decode_encode_bhist,
      dyadicIntervalRefinement_round_trip,
      (fun _ _ heq => dyadicIntervalRefinementToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DyadicIntervalRefinementUp.TasteGate
