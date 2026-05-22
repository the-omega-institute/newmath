import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricCompletionUniquenessUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricCompletionUniquenessUp : Type where
  | mk
      (metricSource denseZero finiteZero separatedReflectionZero separatedCompletionZero denseOne
        finiteOne separatedReflectionOne separatedCompletionOne comparisonLedger transport replay
        provenance localNameCert : BHist) :
      MetricCompletionUniquenessUp
  deriving DecidableEq

def metricCompletionUniquenessEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricCompletionUniquenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricCompletionUniquenessEncodeBHist h

def metricCompletionUniquenessDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricCompletionUniquenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricCompletionUniquenessDecodeBHist tail)

private theorem metricCompletionUniqueness_decode_encode_bhist :
    forall h : BHist,
      metricCompletionUniquenessDecodeBHist
        (metricCompletionUniquenessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricCompletionUniquenessFields : MetricCompletionUniquenessUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCompletionUniquenessUp.mk M E0 F0 R0 S0 E1 F1 R1 S1 Q H C P N =>
      [M, E0, F0, R0, S0, E1, F1, R1, S1, Q, H, C, P, N]

def metricCompletionUniquenessToEventFlow : MetricCompletionUniquenessUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metricCompletionUniquenessFields x).map metricCompletionUniquenessEncodeBHist

private def metricCompletionUniquenessEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      metricCompletionUniquenessEventAtDefault index rest

private def metricCompletionUniquenessExactLength : Nat -> EventFlow -> Bool
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => true
  | Nat.zero, _event :: _rest => false
  | Nat.succ _index, [] => false
  | Nat.succ index, _event :: rest => metricCompletionUniquenessExactLength index rest

def metricCompletionUniquenessFromEventFlow
    (ef : EventFlow) : Option MetricCompletionUniquenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match metricCompletionUniquenessExactLength 14 ef with
  | true =>
      some
        (MetricCompletionUniquenessUp.mk
          (metricCompletionUniquenessDecodeBHist
            (metricCompletionUniquenessEventAtDefault 0 ef))
          (metricCompletionUniquenessDecodeBHist
            (metricCompletionUniquenessEventAtDefault 1 ef))
          (metricCompletionUniquenessDecodeBHist
            (metricCompletionUniquenessEventAtDefault 2 ef))
          (metricCompletionUniquenessDecodeBHist
            (metricCompletionUniquenessEventAtDefault 3 ef))
          (metricCompletionUniquenessDecodeBHist
            (metricCompletionUniquenessEventAtDefault 4 ef))
          (metricCompletionUniquenessDecodeBHist
            (metricCompletionUniquenessEventAtDefault 5 ef))
          (metricCompletionUniquenessDecodeBHist
            (metricCompletionUniquenessEventAtDefault 6 ef))
          (metricCompletionUniquenessDecodeBHist
            (metricCompletionUniquenessEventAtDefault 7 ef))
          (metricCompletionUniquenessDecodeBHist
            (metricCompletionUniquenessEventAtDefault 8 ef))
          (metricCompletionUniquenessDecodeBHist
            (metricCompletionUniquenessEventAtDefault 9 ef))
          (metricCompletionUniquenessDecodeBHist
            (metricCompletionUniquenessEventAtDefault 10 ef))
          (metricCompletionUniquenessDecodeBHist
            (metricCompletionUniquenessEventAtDefault 11 ef))
          (metricCompletionUniquenessDecodeBHist
            (metricCompletionUniquenessEventAtDefault 12 ef))
          (metricCompletionUniquenessDecodeBHist
            (metricCompletionUniquenessEventAtDefault 13 ef)))
  | false => none

private theorem metricCompletionUniqueness_round_trip :
    forall x : MetricCompletionUniquenessUp,
      metricCompletionUniquenessFromEventFlow
        (metricCompletionUniquenessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M E0 F0 R0 S0 E1 F1 R1 S1 Q H C P N =>
      change
        some
          (MetricCompletionUniquenessUp.mk
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist M))
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist E0))
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist F0))
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist R0))
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist S0))
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist E1))
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist F1))
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist R1))
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist S1))
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist Q))
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist H))
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist C))
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist P))
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist N))) =
          some (MetricCompletionUniquenessUp.mk M E0 F0 R0 S0 E1 F1 R1 S1 Q H C P N)
      rw [metricCompletionUniqueness_decode_encode_bhist M,
        metricCompletionUniqueness_decode_encode_bhist E0,
        metricCompletionUniqueness_decode_encode_bhist F0,
        metricCompletionUniqueness_decode_encode_bhist R0,
        metricCompletionUniqueness_decode_encode_bhist S0,
        metricCompletionUniqueness_decode_encode_bhist E1,
        metricCompletionUniqueness_decode_encode_bhist F1,
        metricCompletionUniqueness_decode_encode_bhist R1,
        metricCompletionUniqueness_decode_encode_bhist S1,
        metricCompletionUniqueness_decode_encode_bhist Q,
        metricCompletionUniqueness_decode_encode_bhist H,
        metricCompletionUniqueness_decode_encode_bhist C,
        metricCompletionUniqueness_decode_encode_bhist P,
        metricCompletionUniqueness_decode_encode_bhist N]

private theorem metricCompletionUniquenessToEventFlow_injective
    {x y : MetricCompletionUniquenessUp} :
    metricCompletionUniquenessToEventFlow x = metricCompletionUniquenessToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricCompletionUniquenessFromEventFlow
          (metricCompletionUniquenessToEventFlow x) =
        metricCompletionUniquenessFromEventFlow
          (metricCompletionUniquenessToEventFlow y) :=
    congrArg metricCompletionUniquenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metricCompletionUniqueness_round_trip x).symm
      (Eq.trans hread (metricCompletionUniqueness_round_trip y)))

instance metricCompletionUniquenessBHistCarrier :
    BHistCarrier MetricCompletionUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricCompletionUniquenessToEventFlow
  fromEventFlow := metricCompletionUniquenessFromEventFlow

instance metricCompletionUniquenessChapterTasteGate :
    ChapterTasteGate MetricCompletionUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metricCompletionUniquenessFromEventFlow
        (metricCompletionUniquenessToEventFlow x) = some x
    exact metricCompletionUniqueness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metricCompletionUniquenessToEventFlow_injective heq)

def taste_gate : ChapterTasteGate MetricCompletionUniquenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricCompletionUniquenessChapterTasteGate

theorem MetricCompletionUniquenessTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MetricCompletionUniquenessUp) ∧
      (∀ h : BHist,
        metricCompletionUniquenessDecodeBHist
          (metricCompletionUniquenessEncodeBHist h) = h) ∧
        (∀ x : MetricCompletionUniquenessUp,
          metricCompletionUniquenessFromEventFlow
            (metricCompletionUniquenessToEventFlow x) = some x) ∧
          (∀ x y : MetricCompletionUniquenessUp,
            metricCompletionUniquenessToEventFlow x =
              metricCompletionUniquenessToEventFlow y -> x = y) ∧
            metricCompletionUniquenessEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨metricCompletionUniquenessChapterTasteGate⟩,
      metricCompletionUniqueness_decode_encode_bhist,
      metricCompletionUniqueness_round_trip,
      (fun _ _ heq => metricCompletionUniquenessToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MetricCompletionUniquenessUp.TasteGate
