import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteObservationTraceFilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteObservationTraceFilterUp : Type where
  | mk (O T K A G H C P N : BHist) : FiniteObservationTraceFilterUp
  deriving DecidableEq

def finiteObservationTraceFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteObservationTraceFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteObservationTraceFilterEncodeBHist h

def finiteObservationTraceFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteObservationTraceFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteObservationTraceFilterDecodeBHist tail)

private theorem FiniteObservationTraceFilterTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      finiteObservationTraceFilterDecodeBHist
          (finiteObservationTraceFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteObservationTraceFilterFields :
    FiniteObservationTraceFilterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteObservationTraceFilterUp.mk O T K A G H C P N =>
      [O, T, K, A, G, H, C, P, N]

def finiteObservationTraceFilterToEventFlow :
    FiniteObservationTraceFilterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteObservationTraceFilterFields x).map
      finiteObservationTraceFilterEncodeBHist

private def finiteObservationTraceFilterEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      finiteObservationTraceFilterEventAtDefault index rest

def finiteObservationTraceFilterFromEventFlow :
    EventFlow → Option FiniteObservationTraceFilterUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (FiniteObservationTraceFilterUp.mk
          (finiteObservationTraceFilterDecodeBHist
            (finiteObservationTraceFilterEventAtDefault 0 ef))
          (finiteObservationTraceFilterDecodeBHist
            (finiteObservationTraceFilterEventAtDefault 1 ef))
          (finiteObservationTraceFilterDecodeBHist
            (finiteObservationTraceFilterEventAtDefault 2 ef))
          (finiteObservationTraceFilterDecodeBHist
            (finiteObservationTraceFilterEventAtDefault 3 ef))
          (finiteObservationTraceFilterDecodeBHist
            (finiteObservationTraceFilterEventAtDefault 4 ef))
          (finiteObservationTraceFilterDecodeBHist
            (finiteObservationTraceFilterEventAtDefault 5 ef))
          (finiteObservationTraceFilterDecodeBHist
            (finiteObservationTraceFilterEventAtDefault 6 ef))
          (finiteObservationTraceFilterDecodeBHist
            (finiteObservationTraceFilterEventAtDefault 7 ef))
          (finiteObservationTraceFilterDecodeBHist
            (finiteObservationTraceFilterEventAtDefault 8 ef)))

private theorem FiniteObservationTraceFilterTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteObservationTraceFilterUp,
      finiteObservationTraceFilterFromEventFlow
          (finiteObservationTraceFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O T K A G H C P N =>
      change
        some
          (FiniteObservationTraceFilterUp.mk
            (finiteObservationTraceFilterDecodeBHist
              (finiteObservationTraceFilterEncodeBHist O))
            (finiteObservationTraceFilterDecodeBHist
              (finiteObservationTraceFilterEncodeBHist T))
            (finiteObservationTraceFilterDecodeBHist
              (finiteObservationTraceFilterEncodeBHist K))
            (finiteObservationTraceFilterDecodeBHist
              (finiteObservationTraceFilterEncodeBHist A))
            (finiteObservationTraceFilterDecodeBHist
              (finiteObservationTraceFilterEncodeBHist G))
            (finiteObservationTraceFilterDecodeBHist
              (finiteObservationTraceFilterEncodeBHist H))
            (finiteObservationTraceFilterDecodeBHist
              (finiteObservationTraceFilterEncodeBHist C))
            (finiteObservationTraceFilterDecodeBHist
              (finiteObservationTraceFilterEncodeBHist P))
            (finiteObservationTraceFilterDecodeBHist
              (finiteObservationTraceFilterEncodeBHist N))) =
          some (FiniteObservationTraceFilterUp.mk O T K A G H C P N)
      rw [FiniteObservationTraceFilterTasteGate_single_carrier_alignment_decode O,
        FiniteObservationTraceFilterTasteGate_single_carrier_alignment_decode T,
        FiniteObservationTraceFilterTasteGate_single_carrier_alignment_decode K,
        FiniteObservationTraceFilterTasteGate_single_carrier_alignment_decode A,
        FiniteObservationTraceFilterTasteGate_single_carrier_alignment_decode G,
        FiniteObservationTraceFilterTasteGate_single_carrier_alignment_decode H,
        FiniteObservationTraceFilterTasteGate_single_carrier_alignment_decode C,
        FiniteObservationTraceFilterTasteGate_single_carrier_alignment_decode P,
        FiniteObservationTraceFilterTasteGate_single_carrier_alignment_decode N]

private theorem FiniteObservationTraceFilterTasteGate_single_carrier_alignment_injective
    {x y : FiniteObservationTraceFilterUp} :
    finiteObservationTraceFilterToEventFlow x =
      finiteObservationTraceFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteObservationTraceFilterFromEventFlow
          (finiteObservationTraceFilterToEventFlow x) =
        finiteObservationTraceFilterFromEventFlow
          (finiteObservationTraceFilterToEventFlow y) :=
    congrArg finiteObservationTraceFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteObservationTraceFilterTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteObservationTraceFilterTasteGate_single_carrier_alignment_round_trip y)))

private theorem FiniteObservationTraceFilterTasteGate_single_carrier_alignment_fields :
    ∀ x y : FiniteObservationTraceFilterUp,
      finiteObservationTraceFilterFields x =
        finiteObservationTraceFilterFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk O1 T1 K1 A1 G1 H1 C1 P1 N1 =>
      cases y with
      | mk O2 T2 K2 A2 G2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance finiteObservationTraceFilterBHistCarrier :
    BHistCarrier FiniteObservationTraceFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteObservationTraceFilterToEventFlow
  fromEventFlow := finiteObservationTraceFilterFromEventFlow

instance finiteObservationTraceFilterChapterTasteGate :
    ChapterTasteGate FiniteObservationTraceFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteObservationTraceFilterFromEventFlow
          (finiteObservationTraceFilterToEventFlow x) = some x
    exact FiniteObservationTraceFilterTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (FiniteObservationTraceFilterTasteGate_single_carrier_alignment_injective heq)

instance finiteObservationTraceFilterFieldFaithful :
    FieldFaithful FiniteObservationTraceFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteObservationTraceFilterFields
  field_faithful :=
    FiniteObservationTraceFilterTasteGate_single_carrier_alignment_fields

instance finiteObservationTraceFilterNontrivial :
    Nontrivial FiniteObservationTraceFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteObservationTraceFilterUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteObservationTraceFilterUp.mk (BHist.e0 BHist.Empty)
        (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteObservationTraceFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteObservationTraceFilterChapterTasteGate

theorem FiniteObservationTraceFilterTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteObservationTraceFilterDecodeBHist
        (finiteObservationTraceFilterEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier FiniteObservationTraceFilterUp) ∧
        Nonempty (ChapterTasteGate FiniteObservationTraceFilterUp) ∧
          Nonempty (FieldFaithful FiniteObservationTraceFilterUp) ∧
            Nonempty
              (BEDC.Meta.TasteGate.Nontrivial
                FiniteObservationTraceFilterUp) ∧
              finiteObservationTraceFilterEncodeBHist BHist.Empty =
                ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨FiniteObservationTraceFilterTasteGate_single_carrier_alignment_decode,
      ⟨finiteObservationTraceFilterBHistCarrier⟩,
      ⟨finiteObservationTraceFilterChapterTasteGate⟩,
      ⟨finiteObservationTraceFilterFieldFaithful⟩,
      ⟨finiteObservationTraceFilterNontrivial⟩,
      rfl⟩

end BEDC.Derived.FiniteObservationTraceFilterUp
