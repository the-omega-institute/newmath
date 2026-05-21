import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealSeriesUp : Type where
  | mk (T S W Q D M E H C P N : BHist) : RealSeriesUp
  deriving DecidableEq

def realSeriesEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realSeriesEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realSeriesEncodeBHist h

def realSeriesDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realSeriesDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realSeriesDecodeBHist tail)

private theorem RealSeriesUpTasteGate_single_carrier_alignment_decode :
    forall h : BHist, realSeriesDecodeBHist (realSeriesEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realSeriesToEventFlow : RealSeriesUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealSeriesUp.mk T S W Q D M E H C P N =>
      [[BMark.b0],
        realSeriesEncodeBHist T,
        [BMark.b1, BMark.b0],
        realSeriesEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        realSeriesEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realSeriesEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realSeriesEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realSeriesEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realSeriesEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realSeriesEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realSeriesEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        realSeriesEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realSeriesEncodeBHist N]

private def realSeriesEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realSeriesEventAtDefault index rest

def realSeriesFromEventFlow (ef : EventFlow) : Option RealSeriesUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealSeriesUp.mk
      (realSeriesDecodeBHist (realSeriesEventAtDefault 1 ef))
      (realSeriesDecodeBHist (realSeriesEventAtDefault 3 ef))
      (realSeriesDecodeBHist (realSeriesEventAtDefault 5 ef))
      (realSeriesDecodeBHist (realSeriesEventAtDefault 7 ef))
      (realSeriesDecodeBHist (realSeriesEventAtDefault 9 ef))
      (realSeriesDecodeBHist (realSeriesEventAtDefault 11 ef))
      (realSeriesDecodeBHist (realSeriesEventAtDefault 13 ef))
      (realSeriesDecodeBHist (realSeriesEventAtDefault 15 ef))
      (realSeriesDecodeBHist (realSeriesEventAtDefault 17 ef))
      (realSeriesDecodeBHist (realSeriesEventAtDefault 19 ef))
      (realSeriesDecodeBHist (realSeriesEventAtDefault 21 ef)))

private theorem RealSeriesUpTasteGate_single_carrier_alignment_round_trip :
    forall x : RealSeriesUp, realSeriesFromEventFlow (realSeriesToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T S W Q D M E H C P N =>
      change
        some
          (RealSeriesUp.mk
            (realSeriesDecodeBHist (realSeriesEncodeBHist T))
            (realSeriesDecodeBHist (realSeriesEncodeBHist S))
            (realSeriesDecodeBHist (realSeriesEncodeBHist W))
            (realSeriesDecodeBHist (realSeriesEncodeBHist Q))
            (realSeriesDecodeBHist (realSeriesEncodeBHist D))
            (realSeriesDecodeBHist (realSeriesEncodeBHist M))
            (realSeriesDecodeBHist (realSeriesEncodeBHist E))
            (realSeriesDecodeBHist (realSeriesEncodeBHist H))
            (realSeriesDecodeBHist (realSeriesEncodeBHist C))
            (realSeriesDecodeBHist (realSeriesEncodeBHist P))
            (realSeriesDecodeBHist (realSeriesEncodeBHist N))) =
          some (RealSeriesUp.mk T S W Q D M E H C P N)
      rw [RealSeriesUpTasteGate_single_carrier_alignment_decode T,
        RealSeriesUpTasteGate_single_carrier_alignment_decode S,
        RealSeriesUpTasteGate_single_carrier_alignment_decode W,
        RealSeriesUpTasteGate_single_carrier_alignment_decode Q,
        RealSeriesUpTasteGate_single_carrier_alignment_decode D,
        RealSeriesUpTasteGate_single_carrier_alignment_decode M,
        RealSeriesUpTasteGate_single_carrier_alignment_decode E,
        RealSeriesUpTasteGate_single_carrier_alignment_decode H,
        RealSeriesUpTasteGate_single_carrier_alignment_decode C,
        RealSeriesUpTasteGate_single_carrier_alignment_decode P,
        RealSeriesUpTasteGate_single_carrier_alignment_decode N]

private theorem RealSeriesUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealSeriesUp} :
    realSeriesToEventFlow x = realSeriesToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realSeriesFromEventFlow (realSeriesToEventFlow x) =
        realSeriesFromEventFlow (realSeriesToEventFlow y) :=
    congrArg realSeriesFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealSeriesUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealSeriesUpTasteGate_single_carrier_alignment_round_trip y)))

private def realSeriesFields : RealSeriesUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealSeriesUp.mk T S W Q D M E H C P N => [T, S, W, Q, D, M, E, H, C, P, N]

private theorem RealSeriesUpTasteGate_single_carrier_alignment_fields :
    forall x y : RealSeriesUp, realSeriesFields x = realSeriesFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 S1 W1 Q1 D1 M1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk T2 S2 W2 Q2 D2 M2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance realSeriesBHistCarrier : BHistCarrier RealSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realSeriesToEventFlow
  fromEventFlow := realSeriesFromEventFlow

instance realSeriesChapterTasteGate : ChapterTasteGate RealSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realSeriesFromEventFlow (realSeriesToEventFlow x) = some x
    exact RealSeriesUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealSeriesUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realSeriesFieldFaithful : FieldFaithful RealSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realSeriesFields
  field_faithful := RealSeriesUpTasteGate_single_carrier_alignment_fields

instance realSeriesNontrivial : Nontrivial RealSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealSeriesUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealSeriesUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealSeriesUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realSeriesChapterTasteGate

theorem RealSeriesUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealSeriesUp) ∧
      Nonempty (FieldFaithful RealSeriesUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RealSeriesUp) ∧
          (∀ h : BHist, realSeriesDecodeBHist (realSeriesEncodeBHist h) = h) ∧
            (∀ x : RealSeriesUp, realSeriesFromEventFlow (realSeriesToEventFlow x) = some x) ∧
              (∀ x y : RealSeriesUp,
                realSeriesToEventFlow x = realSeriesToEventFlow y -> x = y) ∧
                realSeriesEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨realSeriesChapterTasteGate⟩,
      ⟨realSeriesFieldFaithful⟩,
      ⟨realSeriesNontrivial⟩,
      RealSeriesUpTasteGate_single_carrier_alignment_decode,
      RealSeriesUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RealSeriesUpTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealSeriesUp
