import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealPowerSeriesUp : Type where
  | mk (A Z X R W S M E H C P N : BHist) : RealPowerSeriesUp
  deriving DecidableEq

def realPowerSeriesEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realPowerSeriesEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realPowerSeriesEncodeBHist h

def realPowerSeriesDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realPowerSeriesDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realPowerSeriesDecodeBHist tail)

private theorem RealPowerSeriesUpTasteGate_single_carrier_alignment_decode :
    forall h : BHist, realPowerSeriesDecodeBHist (realPowerSeriesEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realPowerSeriesToEventFlow : RealPowerSeriesUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealPowerSeriesUp.mk A Z X R W S M E H C P N =>
      [[BMark.b0],
        realPowerSeriesEncodeBHist A,
        [BMark.b1, BMark.b0],
        realPowerSeriesEncodeBHist Z,
        [BMark.b1, BMark.b1, BMark.b0],
        realPowerSeriesEncodeBHist X,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realPowerSeriesEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realPowerSeriesEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realPowerSeriesEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realPowerSeriesEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realPowerSeriesEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realPowerSeriesEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        realPowerSeriesEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realPowerSeriesEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realPowerSeriesEncodeBHist N]

private def realPowerSeriesEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realPowerSeriesEventAtDefault index rest

def realPowerSeriesFromEventFlow (ef : EventFlow) : Option RealPowerSeriesUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealPowerSeriesUp.mk
      (realPowerSeriesDecodeBHist (realPowerSeriesEventAtDefault 1 ef))
      (realPowerSeriesDecodeBHist (realPowerSeriesEventAtDefault 3 ef))
      (realPowerSeriesDecodeBHist (realPowerSeriesEventAtDefault 5 ef))
      (realPowerSeriesDecodeBHist (realPowerSeriesEventAtDefault 7 ef))
      (realPowerSeriesDecodeBHist (realPowerSeriesEventAtDefault 9 ef))
      (realPowerSeriesDecodeBHist (realPowerSeriesEventAtDefault 11 ef))
      (realPowerSeriesDecodeBHist (realPowerSeriesEventAtDefault 13 ef))
      (realPowerSeriesDecodeBHist (realPowerSeriesEventAtDefault 15 ef))
      (realPowerSeriesDecodeBHist (realPowerSeriesEventAtDefault 17 ef))
      (realPowerSeriesDecodeBHist (realPowerSeriesEventAtDefault 19 ef))
      (realPowerSeriesDecodeBHist (realPowerSeriesEventAtDefault 21 ef))
      (realPowerSeriesDecodeBHist (realPowerSeriesEventAtDefault 23 ef)))

private theorem RealPowerSeriesUpTasteGate_single_carrier_alignment_round_trip :
    forall x : RealPowerSeriesUp,
      realPowerSeriesFromEventFlow (realPowerSeriesToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A Z X R W S M E H C P N =>
      change
        some
          (RealPowerSeriesUp.mk
            (realPowerSeriesDecodeBHist (realPowerSeriesEncodeBHist A))
            (realPowerSeriesDecodeBHist (realPowerSeriesEncodeBHist Z))
            (realPowerSeriesDecodeBHist (realPowerSeriesEncodeBHist X))
            (realPowerSeriesDecodeBHist (realPowerSeriesEncodeBHist R))
            (realPowerSeriesDecodeBHist (realPowerSeriesEncodeBHist W))
            (realPowerSeriesDecodeBHist (realPowerSeriesEncodeBHist S))
            (realPowerSeriesDecodeBHist (realPowerSeriesEncodeBHist M))
            (realPowerSeriesDecodeBHist (realPowerSeriesEncodeBHist E))
            (realPowerSeriesDecodeBHist (realPowerSeriesEncodeBHist H))
            (realPowerSeriesDecodeBHist (realPowerSeriesEncodeBHist C))
            (realPowerSeriesDecodeBHist (realPowerSeriesEncodeBHist P))
            (realPowerSeriesDecodeBHist (realPowerSeriesEncodeBHist N))) =
          some (RealPowerSeriesUp.mk A Z X R W S M E H C P N)
      rw [RealPowerSeriesUpTasteGate_single_carrier_alignment_decode A,
        RealPowerSeriesUpTasteGate_single_carrier_alignment_decode Z,
        RealPowerSeriesUpTasteGate_single_carrier_alignment_decode X,
        RealPowerSeriesUpTasteGate_single_carrier_alignment_decode R,
        RealPowerSeriesUpTasteGate_single_carrier_alignment_decode W,
        RealPowerSeriesUpTasteGate_single_carrier_alignment_decode S,
        RealPowerSeriesUpTasteGate_single_carrier_alignment_decode M,
        RealPowerSeriesUpTasteGate_single_carrier_alignment_decode E,
        RealPowerSeriesUpTasteGate_single_carrier_alignment_decode H,
        RealPowerSeriesUpTasteGate_single_carrier_alignment_decode C,
        RealPowerSeriesUpTasteGate_single_carrier_alignment_decode P,
        RealPowerSeriesUpTasteGate_single_carrier_alignment_decode N]

private theorem RealPowerSeriesUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealPowerSeriesUp} :
    realPowerSeriesToEventFlow x = realPowerSeriesToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realPowerSeriesFromEventFlow (realPowerSeriesToEventFlow x) =
        realPowerSeriesFromEventFlow (realPowerSeriesToEventFlow y) :=
    congrArg realPowerSeriesFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealPowerSeriesUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealPowerSeriesUpTasteGate_single_carrier_alignment_round_trip y)))

private def realPowerSeriesFields : RealPowerSeriesUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealPowerSeriesUp.mk A Z X R W S M E H C P N => [A, Z, X, R, W, S, M, E, H, C, P, N]

private theorem RealPowerSeriesUpTasteGate_single_carrier_alignment_fields :
    forall x y : RealPowerSeriesUp,
      realPowerSeriesFields x = realPowerSeriesFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 Z1 X1 R1 W1 S1 M1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk A2 Z2 X2 R2 W2 S2 M2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance realPowerSeriesBHistCarrier : BHistCarrier RealPowerSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realPowerSeriesToEventFlow
  fromEventFlow := realPowerSeriesFromEventFlow

instance realPowerSeriesChapterTasteGate : ChapterTasteGate RealPowerSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realPowerSeriesFromEventFlow (realPowerSeriesToEventFlow x) = some x
    exact RealPowerSeriesUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealPowerSeriesUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realPowerSeriesFieldFaithful : FieldFaithful RealPowerSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realPowerSeriesFields
  field_faithful := RealPowerSeriesUpTasteGate_single_carrier_alignment_fields

instance realPowerSeriesNontrivial : Nontrivial RealPowerSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealPowerSeriesUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealPowerSeriesUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealPowerSeriesUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realPowerSeriesChapterTasteGate

theorem RealPowerSeriesUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealPowerSeriesUp) ∧
      Nonempty (FieldFaithful RealPowerSeriesUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RealPowerSeriesUp) ∧
          (∀ h : BHist,
            realPowerSeriesDecodeBHist (realPowerSeriesEncodeBHist h) = h) ∧
            (∀ x : RealPowerSeriesUp,
              realPowerSeriesFromEventFlow (realPowerSeriesToEventFlow x) = some x) ∧
              (∀ x y : RealPowerSeriesUp,
                realPowerSeriesToEventFlow x = realPowerSeriesToEventFlow y -> x = y) ∧
                realPowerSeriesEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨realPowerSeriesChapterTasteGate⟩,
      ⟨realPowerSeriesFieldFaithful⟩,
      ⟨realPowerSeriesNontrivial⟩,
      RealPowerSeriesUpTasteGate_single_carrier_alignment_decode,
      RealPowerSeriesUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RealPowerSeriesUpTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealPowerSeriesUp
