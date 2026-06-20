import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRegularComparisonSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRegularComparisonSealUp : Type where
  | mk (A B D WA WB RA RB Q EA EB H K P N : BHist) : CauchyRegularComparisonSealUp
  deriving DecidableEq

def cauchyRegularComparisonSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRegularComparisonSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRegularComparisonSealEncodeBHist h

def cauchyRegularComparisonSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRegularComparisonSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRegularComparisonSealDecodeBHist tail)

private theorem CauchyRegularComparisonSealTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyRegularComparisonSealDecodeBHist (cauchyRegularComparisonSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyRegularComparisonSealFields : CauchyRegularComparisonSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRegularComparisonSealUp.mk A B D WA WB RA RB Q EA EB H K P N =>
      [A, B, D, WA, WB, RA, RB, Q, EA, EB, H, K, P, N]

def cauchyRegularComparisonSealToEventFlow : CauchyRegularComparisonSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyRegularComparisonSealFields x).map cauchyRegularComparisonSealEncodeBHist

private def CauchyRegularComparisonSealTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CauchyRegularComparisonSealTasteGate_single_carrier_alignment_eventAt index rest

def cauchyRegularComparisonSealFromEventFlow (ef : EventFlow) :
    Option CauchyRegularComparisonSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyRegularComparisonSealUp.mk
      (cauchyRegularComparisonSealDecodeBHist
        (CauchyRegularComparisonSealTasteGate_single_carrier_alignment_eventAt 0 ef))
      (cauchyRegularComparisonSealDecodeBHist
        (CauchyRegularComparisonSealTasteGate_single_carrier_alignment_eventAt 1 ef))
      (cauchyRegularComparisonSealDecodeBHist
        (CauchyRegularComparisonSealTasteGate_single_carrier_alignment_eventAt 2 ef))
      (cauchyRegularComparisonSealDecodeBHist
        (CauchyRegularComparisonSealTasteGate_single_carrier_alignment_eventAt 3 ef))
      (cauchyRegularComparisonSealDecodeBHist
        (CauchyRegularComparisonSealTasteGate_single_carrier_alignment_eventAt 4 ef))
      (cauchyRegularComparisonSealDecodeBHist
        (CauchyRegularComparisonSealTasteGate_single_carrier_alignment_eventAt 5 ef))
      (cauchyRegularComparisonSealDecodeBHist
        (CauchyRegularComparisonSealTasteGate_single_carrier_alignment_eventAt 6 ef))
      (cauchyRegularComparisonSealDecodeBHist
        (CauchyRegularComparisonSealTasteGate_single_carrier_alignment_eventAt 7 ef))
      (cauchyRegularComparisonSealDecodeBHist
        (CauchyRegularComparisonSealTasteGate_single_carrier_alignment_eventAt 8 ef))
      (cauchyRegularComparisonSealDecodeBHist
        (CauchyRegularComparisonSealTasteGate_single_carrier_alignment_eventAt 9 ef))
      (cauchyRegularComparisonSealDecodeBHist
        (CauchyRegularComparisonSealTasteGate_single_carrier_alignment_eventAt 10 ef))
      (cauchyRegularComparisonSealDecodeBHist
        (CauchyRegularComparisonSealTasteGate_single_carrier_alignment_eventAt 11 ef))
      (cauchyRegularComparisonSealDecodeBHist
        (CauchyRegularComparisonSealTasteGate_single_carrier_alignment_eventAt 12 ef))
      (cauchyRegularComparisonSealDecodeBHist
        (CauchyRegularComparisonSealTasteGate_single_carrier_alignment_eventAt 13 ef)))

private theorem CauchyRegularComparisonSealTasteGate_single_carrier_alignment_round_trip
    (x : CauchyRegularComparisonSealUp) :
    cauchyRegularComparisonSealFromEventFlow (cauchyRegularComparisonSealToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A B D WA WB RA RB Q EA EB H K P N =>
      change
        some
          (CauchyRegularComparisonSealUp.mk
            (cauchyRegularComparisonSealDecodeBHist
              (cauchyRegularComparisonSealEncodeBHist A))
            (cauchyRegularComparisonSealDecodeBHist
              (cauchyRegularComparisonSealEncodeBHist B))
            (cauchyRegularComparisonSealDecodeBHist
              (cauchyRegularComparisonSealEncodeBHist D))
            (cauchyRegularComparisonSealDecodeBHist
              (cauchyRegularComparisonSealEncodeBHist WA))
            (cauchyRegularComparisonSealDecodeBHist
              (cauchyRegularComparisonSealEncodeBHist WB))
            (cauchyRegularComparisonSealDecodeBHist
              (cauchyRegularComparisonSealEncodeBHist RA))
            (cauchyRegularComparisonSealDecodeBHist
              (cauchyRegularComparisonSealEncodeBHist RB))
            (cauchyRegularComparisonSealDecodeBHist
              (cauchyRegularComparisonSealEncodeBHist Q))
            (cauchyRegularComparisonSealDecodeBHist
              (cauchyRegularComparisonSealEncodeBHist EA))
            (cauchyRegularComparisonSealDecodeBHist
              (cauchyRegularComparisonSealEncodeBHist EB))
            (cauchyRegularComparisonSealDecodeBHist
              (cauchyRegularComparisonSealEncodeBHist H))
            (cauchyRegularComparisonSealDecodeBHist
              (cauchyRegularComparisonSealEncodeBHist K))
            (cauchyRegularComparisonSealDecodeBHist
              (cauchyRegularComparisonSealEncodeBHist P))
            (cauchyRegularComparisonSealDecodeBHist
              (cauchyRegularComparisonSealEncodeBHist N))) =
          some (CauchyRegularComparisonSealUp.mk A B D WA WB RA RB Q EA EB H K P N)
      rw [CauchyRegularComparisonSealTasteGate_single_carrier_alignment_decode_encode A,
        CauchyRegularComparisonSealTasteGate_single_carrier_alignment_decode_encode B,
        CauchyRegularComparisonSealTasteGate_single_carrier_alignment_decode_encode D,
        CauchyRegularComparisonSealTasteGate_single_carrier_alignment_decode_encode WA,
        CauchyRegularComparisonSealTasteGate_single_carrier_alignment_decode_encode WB,
        CauchyRegularComparisonSealTasteGate_single_carrier_alignment_decode_encode RA,
        CauchyRegularComparisonSealTasteGate_single_carrier_alignment_decode_encode RB,
        CauchyRegularComparisonSealTasteGate_single_carrier_alignment_decode_encode Q,
        CauchyRegularComparisonSealTasteGate_single_carrier_alignment_decode_encode EA,
        CauchyRegularComparisonSealTasteGate_single_carrier_alignment_decode_encode EB,
        CauchyRegularComparisonSealTasteGate_single_carrier_alignment_decode_encode H,
        CauchyRegularComparisonSealTasteGate_single_carrier_alignment_decode_encode K,
        CauchyRegularComparisonSealTasteGate_single_carrier_alignment_decode_encode P,
        CauchyRegularComparisonSealTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyRegularComparisonSealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyRegularComparisonSealUp} :
    cauchyRegularComparisonSealToEventFlow x = cauchyRegularComparisonSealToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRegularComparisonSealFromEventFlow (cauchyRegularComparisonSealToEventFlow x) =
        cauchyRegularComparisonSealFromEventFlow (cauchyRegularComparisonSealToEventFlow y) :=
    congrArg cauchyRegularComparisonSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyRegularComparisonSealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyRegularComparisonSealTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyRegularComparisonSealBHistCarrier : BHistCarrier CauchyRegularComparisonSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRegularComparisonSealToEventFlow
  fromEventFlow := cauchyRegularComparisonSealFromEventFlow

instance cauchyRegularComparisonSealChapterTasteGate :
    ChapterTasteGate CauchyRegularComparisonSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyRegularComparisonSealFromEventFlow (cauchyRegularComparisonSealToEventFlow x) =
        some x
    exact CauchyRegularComparisonSealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyRegularComparisonSealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyRegularComparisonSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyRegularComparisonSealChapterTasteGate

theorem CauchyRegularComparisonSealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyRegularComparisonSealDecodeBHist (cauchyRegularComparisonSealEncodeBHist h) = h) ∧
      (∀ x : CauchyRegularComparisonSealUp,
        cauchyRegularComparisonSealFromEventFlow (cauchyRegularComparisonSealToEventFlow x) =
          some x) ∧
        (∀ x y : CauchyRegularComparisonSealUp,
          cauchyRegularComparisonSealToEventFlow x = cauchyRegularComparisonSealToEventFlow y →
            x = y) ∧
          cauchyRegularComparisonSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyRegularComparisonSealTasteGate_single_carrier_alignment_decode_encode,
      CauchyRegularComparisonSealTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyRegularComparisonSealTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyRegularComparisonSealUp
