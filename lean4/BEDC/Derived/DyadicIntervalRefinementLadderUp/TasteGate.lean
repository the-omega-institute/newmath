import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicIntervalRefinementLadderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicIntervalRefinementLadderUp : Type where
  | mk (I J d E S R A H C P N : BHist) : DyadicIntervalRefinementLadderUp
  deriving DecidableEq

def dyadicIntervalRefinementLadderEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicIntervalRefinementLadderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicIntervalRefinementLadderEncodeBHist h

def dyadicIntervalRefinementLadderDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicIntervalRefinementLadderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicIntervalRefinementLadderDecodeBHist tail)

private theorem DyadicIntervalRefinementLadderTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      dyadicIntervalRefinementLadderDecodeBHist
        (dyadicIntervalRefinementLadderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicIntervalRefinementLadderFields :
    DyadicIntervalRefinementLadderUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicIntervalRefinementLadderUp.mk I J d E S R A H C P N =>
      [I, J, d, E, S, R, A, H, C, P, N]

def dyadicIntervalRefinementLadderToEventFlow :
    DyadicIntervalRefinementLadderUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicIntervalRefinementLadderFields x).map
      dyadicIntervalRefinementLadderEncodeBHist

private def dyadicIntervalRefinementLadderEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      dyadicIntervalRefinementLadderEventAtDefault index rest

def dyadicIntervalRefinementLadderFromEventFlow
    (ef : EventFlow) : Option DyadicIntervalRefinementLadderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicIntervalRefinementLadderUp.mk
      (dyadicIntervalRefinementLadderDecodeBHist
        (dyadicIntervalRefinementLadderEventAtDefault 0 ef))
      (dyadicIntervalRefinementLadderDecodeBHist
        (dyadicIntervalRefinementLadderEventAtDefault 1 ef))
      (dyadicIntervalRefinementLadderDecodeBHist
        (dyadicIntervalRefinementLadderEventAtDefault 2 ef))
      (dyadicIntervalRefinementLadderDecodeBHist
        (dyadicIntervalRefinementLadderEventAtDefault 3 ef))
      (dyadicIntervalRefinementLadderDecodeBHist
        (dyadicIntervalRefinementLadderEventAtDefault 4 ef))
      (dyadicIntervalRefinementLadderDecodeBHist
        (dyadicIntervalRefinementLadderEventAtDefault 5 ef))
      (dyadicIntervalRefinementLadderDecodeBHist
        (dyadicIntervalRefinementLadderEventAtDefault 6 ef))
      (dyadicIntervalRefinementLadderDecodeBHist
        (dyadicIntervalRefinementLadderEventAtDefault 7 ef))
      (dyadicIntervalRefinementLadderDecodeBHist
        (dyadicIntervalRefinementLadderEventAtDefault 8 ef))
      (dyadicIntervalRefinementLadderDecodeBHist
        (dyadicIntervalRefinementLadderEventAtDefault 9 ef))
      (dyadicIntervalRefinementLadderDecodeBHist
        (dyadicIntervalRefinementLadderEventAtDefault 10 ef)))

private theorem DyadicIntervalRefinementLadderTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DyadicIntervalRefinementLadderUp,
      dyadicIntervalRefinementLadderFromEventFlow
        (dyadicIntervalRefinementLadderToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I J d E S R A H C P N =>
      change
        some
          (DyadicIntervalRefinementLadderUp.mk
            (dyadicIntervalRefinementLadderDecodeBHist
              (dyadicIntervalRefinementLadderEncodeBHist I))
            (dyadicIntervalRefinementLadderDecodeBHist
              (dyadicIntervalRefinementLadderEncodeBHist J))
            (dyadicIntervalRefinementLadderDecodeBHist
              (dyadicIntervalRefinementLadderEncodeBHist d))
            (dyadicIntervalRefinementLadderDecodeBHist
              (dyadicIntervalRefinementLadderEncodeBHist E))
            (dyadicIntervalRefinementLadderDecodeBHist
              (dyadicIntervalRefinementLadderEncodeBHist S))
            (dyadicIntervalRefinementLadderDecodeBHist
              (dyadicIntervalRefinementLadderEncodeBHist R))
            (dyadicIntervalRefinementLadderDecodeBHist
              (dyadicIntervalRefinementLadderEncodeBHist A))
            (dyadicIntervalRefinementLadderDecodeBHist
              (dyadicIntervalRefinementLadderEncodeBHist H))
            (dyadicIntervalRefinementLadderDecodeBHist
              (dyadicIntervalRefinementLadderEncodeBHist C))
            (dyadicIntervalRefinementLadderDecodeBHist
              (dyadicIntervalRefinementLadderEncodeBHist P))
            (dyadicIntervalRefinementLadderDecodeBHist
              (dyadicIntervalRefinementLadderEncodeBHist N))) =
          some (DyadicIntervalRefinementLadderUp.mk I J d E S R A H C P N)
      rw [DyadicIntervalRefinementLadderTasteGate_single_carrier_alignment_decode I,
        DyadicIntervalRefinementLadderTasteGate_single_carrier_alignment_decode J,
        DyadicIntervalRefinementLadderTasteGate_single_carrier_alignment_decode d,
        DyadicIntervalRefinementLadderTasteGate_single_carrier_alignment_decode E,
        DyadicIntervalRefinementLadderTasteGate_single_carrier_alignment_decode S,
        DyadicIntervalRefinementLadderTasteGate_single_carrier_alignment_decode R,
        DyadicIntervalRefinementLadderTasteGate_single_carrier_alignment_decode A,
        DyadicIntervalRefinementLadderTasteGate_single_carrier_alignment_decode H,
        DyadicIntervalRefinementLadderTasteGate_single_carrier_alignment_decode C,
        DyadicIntervalRefinementLadderTasteGate_single_carrier_alignment_decode P,
        DyadicIntervalRefinementLadderTasteGate_single_carrier_alignment_decode N]

private theorem dyadicIntervalRefinementLadderToEventFlow_injective
    {x y : DyadicIntervalRefinementLadderUp} :
    dyadicIntervalRefinementLadderToEventFlow x =
      dyadicIntervalRefinementLadderToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicIntervalRefinementLadderFromEventFlow
          (dyadicIntervalRefinementLadderToEventFlow x) =
        dyadicIntervalRefinementLadderFromEventFlow
          (dyadicIntervalRefinementLadderToEventFlow y) :=
    congrArg dyadicIntervalRefinementLadderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DyadicIntervalRefinementLadderTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicIntervalRefinementLadderTasteGate_single_carrier_alignment_round_trip y)))

private theorem dyadicIntervalRefinementLadderFieldFaithful_fields :
    ∀ x y : DyadicIntervalRefinementLadderUp,
      dyadicIntervalRefinementLadderFields x =
        dyadicIntervalRefinementLadderFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 J1 d1 E1 S1 R1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 J2 d2 E2 S2 R2 A2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance dyadicIntervalRefinementLadderBHistCarrier :
    BHistCarrier DyadicIntervalRefinementLadderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicIntervalRefinementLadderToEventFlow
  fromEventFlow := dyadicIntervalRefinementLadderFromEventFlow

instance dyadicIntervalRefinementLadderChapterTasteGate :
    ChapterTasteGate DyadicIntervalRefinementLadderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dyadicIntervalRefinementLadderFromEventFlow
        (dyadicIntervalRefinementLadderToEventFlow x) = some x
    exact DyadicIntervalRefinementLadderTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicIntervalRefinementLadderToEventFlow_injective heq)

instance dyadicIntervalRefinementLadderFieldFaithful :
    FieldFaithful DyadicIntervalRefinementLadderUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicIntervalRefinementLadderFields
  field_faithful := dyadicIntervalRefinementLadderFieldFaithful_fields

instance dyadicIntervalRefinementLadderNontrivial :
    Nontrivial DyadicIntervalRefinementLadderUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicIntervalRefinementLadderUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicIntervalRefinementLadderUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicIntervalRefinementLadderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicIntervalRefinementLadderChapterTasteGate

theorem DyadicIntervalRefinementLadderTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dyadicIntervalRefinementLadderDecodeBHist
        (dyadicIntervalRefinementLadderEncodeBHist h) = h) ∧
      (∀ x : DyadicIntervalRefinementLadderUp,
        dyadicIntervalRefinementLadderFromEventFlow
          (dyadicIntervalRefinementLadderToEventFlow x) = some x) ∧
        (∀ x y : DyadicIntervalRefinementLadderUp,
          dyadicIntervalRefinementLadderToEventFlow x =
            dyadicIntervalRefinementLadderToEventFlow y → x = y) ∧
          dyadicIntervalRefinementLadderEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨DyadicIntervalRefinementLadderTasteGate_single_carrier_alignment_decode,
      DyadicIntervalRefinementLadderTasteGate_single_carrier_alignment_round_trip,
      fun _x _y heq => dyadicIntervalRefinementLadderToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.DyadicIntervalRefinementLadderUp
