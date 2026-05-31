import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SeriesDivergenceTestUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SeriesDivergenceTestUp : Type where
  | mk (A W D T R E H C P N : BHist) : SeriesDivergenceTestUp
  deriving DecidableEq

def seriesDivergenceTestEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: seriesDivergenceTestEncodeBHist h
  | BHist.e1 h => BMark.b1 :: seriesDivergenceTestEncodeBHist h

def seriesDivergenceTestDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (seriesDivergenceTestDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (seriesDivergenceTestDecodeBHist tail)

private theorem SeriesDivergenceTestTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, seriesDivergenceTestDecodeBHist (seriesDivergenceTestEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def seriesDivergenceTestEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => seriesDivergenceTestEventAtDefault index rest

def seriesDivergenceTestToEventFlow : SeriesDivergenceTestUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SeriesDivergenceTestUp.mk A W D T R E H C P N =>
      [seriesDivergenceTestEncodeBHist A,
        seriesDivergenceTestEncodeBHist W,
        seriesDivergenceTestEncodeBHist D,
        seriesDivergenceTestEncodeBHist T,
        seriesDivergenceTestEncodeBHist R,
        seriesDivergenceTestEncodeBHist E,
        seriesDivergenceTestEncodeBHist H,
        seriesDivergenceTestEncodeBHist C,
        seriesDivergenceTestEncodeBHist P,
        seriesDivergenceTestEncodeBHist N]

def seriesDivergenceTestFromEventFlow (ef : EventFlow) : Option SeriesDivergenceTestUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SeriesDivergenceTestUp.mk
      (seriesDivergenceTestDecodeBHist (seriesDivergenceTestEventAtDefault 0 ef))
      (seriesDivergenceTestDecodeBHist (seriesDivergenceTestEventAtDefault 1 ef))
      (seriesDivergenceTestDecodeBHist (seriesDivergenceTestEventAtDefault 2 ef))
      (seriesDivergenceTestDecodeBHist (seriesDivergenceTestEventAtDefault 3 ef))
      (seriesDivergenceTestDecodeBHist (seriesDivergenceTestEventAtDefault 4 ef))
      (seriesDivergenceTestDecodeBHist (seriesDivergenceTestEventAtDefault 5 ef))
      (seriesDivergenceTestDecodeBHist (seriesDivergenceTestEventAtDefault 6 ef))
      (seriesDivergenceTestDecodeBHist (seriesDivergenceTestEventAtDefault 7 ef))
      (seriesDivergenceTestDecodeBHist (seriesDivergenceTestEventAtDefault 8 ef))
      (seriesDivergenceTestDecodeBHist (seriesDivergenceTestEventAtDefault 9 ef)))

private theorem SeriesDivergenceTestTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SeriesDivergenceTestUp,
      seriesDivergenceTestFromEventFlow (seriesDivergenceTestToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A W D T R E H C P N =>
      change
        some
          (SeriesDivergenceTestUp.mk
            (seriesDivergenceTestDecodeBHist (seriesDivergenceTestEncodeBHist A))
            (seriesDivergenceTestDecodeBHist (seriesDivergenceTestEncodeBHist W))
            (seriesDivergenceTestDecodeBHist (seriesDivergenceTestEncodeBHist D))
            (seriesDivergenceTestDecodeBHist (seriesDivergenceTestEncodeBHist T))
            (seriesDivergenceTestDecodeBHist (seriesDivergenceTestEncodeBHist R))
            (seriesDivergenceTestDecodeBHist (seriesDivergenceTestEncodeBHist E))
            (seriesDivergenceTestDecodeBHist (seriesDivergenceTestEncodeBHist H))
            (seriesDivergenceTestDecodeBHist (seriesDivergenceTestEncodeBHist C))
            (seriesDivergenceTestDecodeBHist (seriesDivergenceTestEncodeBHist P))
            (seriesDivergenceTestDecodeBHist (seriesDivergenceTestEncodeBHist N))) =
          some (SeriesDivergenceTestUp.mk A W D T R E H C P N)
      rw [SeriesDivergenceTestTasteGate_single_carrier_alignment_decode_encode A,
        SeriesDivergenceTestTasteGate_single_carrier_alignment_decode_encode W,
        SeriesDivergenceTestTasteGate_single_carrier_alignment_decode_encode D,
        SeriesDivergenceTestTasteGate_single_carrier_alignment_decode_encode T,
        SeriesDivergenceTestTasteGate_single_carrier_alignment_decode_encode R,
        SeriesDivergenceTestTasteGate_single_carrier_alignment_decode_encode E,
        SeriesDivergenceTestTasteGate_single_carrier_alignment_decode_encode H,
        SeriesDivergenceTestTasteGate_single_carrier_alignment_decode_encode C,
        SeriesDivergenceTestTasteGate_single_carrier_alignment_decode_encode P,
        SeriesDivergenceTestTasteGate_single_carrier_alignment_decode_encode N]

private theorem SeriesDivergenceTestTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SeriesDivergenceTestUp} :
    seriesDivergenceTestToEventFlow x = seriesDivergenceTestToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      seriesDivergenceTestFromEventFlow (seriesDivergenceTestToEventFlow x) =
        seriesDivergenceTestFromEventFlow (seriesDivergenceTestToEventFlow y) :=
    congrArg seriesDivergenceTestFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SeriesDivergenceTestTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SeriesDivergenceTestTasteGate_single_carrier_alignment_round_trip y)))

private def seriesDivergenceTestFields : SeriesDivergenceTestUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SeriesDivergenceTestUp.mk A W D T R E H C P N => [A, W, D, T, R, E, H, C, P, N]

private theorem SeriesDivergenceTestTasteGate_single_carrier_alignment_fields :
    ∀ x y : SeriesDivergenceTestUp, seriesDivergenceTestFields x = seriesDivergenceTestFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 W1 D1 T1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk A2 W2 D2 T2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance seriesDivergenceTestBHistCarrier : BHistCarrier SeriesDivergenceTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := seriesDivergenceTestToEventFlow
  fromEventFlow := seriesDivergenceTestFromEventFlow

instance seriesDivergenceTestChapterTasteGate : ChapterTasteGate SeriesDivergenceTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change seriesDivergenceTestFromEventFlow (seriesDivergenceTestToEventFlow x) = some x
    exact SeriesDivergenceTestTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SeriesDivergenceTestTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance seriesDivergenceTestFieldFaithful : FieldFaithful SeriesDivergenceTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := seriesDivergenceTestFields
  field_faithful := SeriesDivergenceTestTasteGate_single_carrier_alignment_fields

instance seriesDivergenceTestNontrivial : BEDC.Meta.TasteGate.Nontrivial SeriesDivergenceTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SeriesDivergenceTestUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SeriesDivergenceTestUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SeriesDivergenceTestUp :=
  -- BEDC touchpoint anchor: BHist BMark
  seriesDivergenceTestChapterTasteGate

theorem SeriesDivergenceTestTasteGate_single_carrier_alignment :
    (∀ h : BHist, seriesDivergenceTestDecodeBHist (seriesDivergenceTestEncodeBHist h) = h) ∧
      (∀ x : SeriesDivergenceTestUp,
        seriesDivergenceTestFromEventFlow (seriesDivergenceTestToEventFlow x) = some x) ∧
        (∀ x y : SeriesDivergenceTestUp,
          seriesDivergenceTestToEventFlow x = seriesDivergenceTestToEventFlow y → x = y) ∧
          seriesDivergenceTestEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨SeriesDivergenceTestTasteGate_single_carrier_alignment_decode_encode,
      SeriesDivergenceTestTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => SeriesDivergenceTestTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SeriesDivergenceTestUp
