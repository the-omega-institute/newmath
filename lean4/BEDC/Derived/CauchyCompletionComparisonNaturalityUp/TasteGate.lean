import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionComparisonNaturalityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionComparisonNaturalityUp : Type where
  | mk (Q U V F R S D E H C P N : BHist) : CauchyCompletionComparisonNaturalityUp
  deriving DecidableEq

def cauchyCompletionComparisonNaturalityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionComparisonNaturalityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionComparisonNaturalityEncodeBHist h

def cauchyCompletionComparisonNaturalityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionComparisonNaturalityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionComparisonNaturalityDecodeBHist tail)

private theorem cauchyCompletionComparisonNaturality_decode_encode :
    ∀ h : BHist,
      cauchyCompletionComparisonNaturalityDecodeBHist
          (cauchyCompletionComparisonNaturalityEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionComparisonNaturalityFields :
    CauchyCompletionComparisonNaturalityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionComparisonNaturalityUp.mk Q U V F R S D E H C P N =>
      [Q, U, V, F, R, S, D, E, H, C, P, N]

def cauchyCompletionComparisonNaturalityToEventFlow :
    CauchyCompletionComparisonNaturalityUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (cauchyCompletionComparisonNaturalityFields x).map
      cauchyCompletionComparisonNaturalityEncodeBHist

private def cauchyCompletionComparisonNaturalityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyCompletionComparisonNaturalityEventAtDefault index rest

def cauchyCompletionComparisonNaturalityFromEventFlow
    (ef : EventFlow) : Option CauchyCompletionComparisonNaturalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionComparisonNaturalityUp.mk
      (cauchyCompletionComparisonNaturalityDecodeBHist
        (cauchyCompletionComparisonNaturalityEventAtDefault 0 ef))
      (cauchyCompletionComparisonNaturalityDecodeBHist
        (cauchyCompletionComparisonNaturalityEventAtDefault 1 ef))
      (cauchyCompletionComparisonNaturalityDecodeBHist
        (cauchyCompletionComparisonNaturalityEventAtDefault 2 ef))
      (cauchyCompletionComparisonNaturalityDecodeBHist
        (cauchyCompletionComparisonNaturalityEventAtDefault 3 ef))
      (cauchyCompletionComparisonNaturalityDecodeBHist
        (cauchyCompletionComparisonNaturalityEventAtDefault 4 ef))
      (cauchyCompletionComparisonNaturalityDecodeBHist
        (cauchyCompletionComparisonNaturalityEventAtDefault 5 ef))
      (cauchyCompletionComparisonNaturalityDecodeBHist
        (cauchyCompletionComparisonNaturalityEventAtDefault 6 ef))
      (cauchyCompletionComparisonNaturalityDecodeBHist
        (cauchyCompletionComparisonNaturalityEventAtDefault 7 ef))
      (cauchyCompletionComparisonNaturalityDecodeBHist
        (cauchyCompletionComparisonNaturalityEventAtDefault 8 ef))
      (cauchyCompletionComparisonNaturalityDecodeBHist
        (cauchyCompletionComparisonNaturalityEventAtDefault 9 ef))
      (cauchyCompletionComparisonNaturalityDecodeBHist
        (cauchyCompletionComparisonNaturalityEventAtDefault 10 ef))
      (cauchyCompletionComparisonNaturalityDecodeBHist
        (cauchyCompletionComparisonNaturalityEventAtDefault 11 ef)))

private theorem cauchyCompletionComparisonNaturality_round_trip
    (x : CauchyCompletionComparisonNaturalityUp) :
    cauchyCompletionComparisonNaturalityFromEventFlow
        (cauchyCompletionComparisonNaturalityToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Q U V F R S D E H C P N =>
      change
        some
            (CauchyCompletionComparisonNaturalityUp.mk
              (cauchyCompletionComparisonNaturalityDecodeBHist
                (cauchyCompletionComparisonNaturalityEncodeBHist Q))
              (cauchyCompletionComparisonNaturalityDecodeBHist
                (cauchyCompletionComparisonNaturalityEncodeBHist U))
              (cauchyCompletionComparisonNaturalityDecodeBHist
                (cauchyCompletionComparisonNaturalityEncodeBHist V))
              (cauchyCompletionComparisonNaturalityDecodeBHist
                (cauchyCompletionComparisonNaturalityEncodeBHist F))
              (cauchyCompletionComparisonNaturalityDecodeBHist
                (cauchyCompletionComparisonNaturalityEncodeBHist R))
              (cauchyCompletionComparisonNaturalityDecodeBHist
                (cauchyCompletionComparisonNaturalityEncodeBHist S))
              (cauchyCompletionComparisonNaturalityDecodeBHist
                (cauchyCompletionComparisonNaturalityEncodeBHist D))
              (cauchyCompletionComparisonNaturalityDecodeBHist
                (cauchyCompletionComparisonNaturalityEncodeBHist E))
              (cauchyCompletionComparisonNaturalityDecodeBHist
                (cauchyCompletionComparisonNaturalityEncodeBHist H))
              (cauchyCompletionComparisonNaturalityDecodeBHist
                (cauchyCompletionComparisonNaturalityEncodeBHist C))
              (cauchyCompletionComparisonNaturalityDecodeBHist
                (cauchyCompletionComparisonNaturalityEncodeBHist P))
              (cauchyCompletionComparisonNaturalityDecodeBHist
                (cauchyCompletionComparisonNaturalityEncodeBHist N))) =
          some (CauchyCompletionComparisonNaturalityUp.mk Q U V F R S D E H C P N)
      rw [cauchyCompletionComparisonNaturality_decode_encode Q,
        cauchyCompletionComparisonNaturality_decode_encode U,
        cauchyCompletionComparisonNaturality_decode_encode V,
        cauchyCompletionComparisonNaturality_decode_encode F,
        cauchyCompletionComparisonNaturality_decode_encode R,
        cauchyCompletionComparisonNaturality_decode_encode S,
        cauchyCompletionComparisonNaturality_decode_encode D,
        cauchyCompletionComparisonNaturality_decode_encode E,
        cauchyCompletionComparisonNaturality_decode_encode H,
        cauchyCompletionComparisonNaturality_decode_encode C,
        cauchyCompletionComparisonNaturality_decode_encode P,
        cauchyCompletionComparisonNaturality_decode_encode N]

private theorem cauchyCompletionComparisonNaturalityToEventFlow_injective
    {x y : CauchyCompletionComparisonNaturalityUp} :
    cauchyCompletionComparisonNaturalityToEventFlow x =
      cauchyCompletionComparisonNaturalityToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionComparisonNaturalityFromEventFlow
          (cauchyCompletionComparisonNaturalityToEventFlow x) =
        cauchyCompletionComparisonNaturalityFromEventFlow
          (cauchyCompletionComparisonNaturalityToEventFlow y) :=
    congrArg cauchyCompletionComparisonNaturalityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyCompletionComparisonNaturality_round_trip x).symm
      (Eq.trans hread (cauchyCompletionComparisonNaturality_round_trip y)))

instance cauchyCompletionComparisonNaturalityBHistCarrier :
    BHistCarrier CauchyCompletionComparisonNaturalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionComparisonNaturalityToEventFlow
  fromEventFlow := cauchyCompletionComparisonNaturalityFromEventFlow

instance cauchyCompletionComparisonNaturalityChapterTasteGate :
    ChapterTasteGate CauchyCompletionComparisonNaturalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := cauchyCompletionComparisonNaturality_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletionComparisonNaturalityToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyCompletionComparisonNaturalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionComparisonNaturalityChapterTasteGate

theorem CauchyCompletionComparisonNaturalityTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CauchyCompletionComparisonNaturalityUp) ∧
      Nonempty (ChapterTasteGate CauchyCompletionComparisonNaturalityUp) ∧
        (∀ x : CauchyCompletionComparisonNaturalityUp,
          cauchyCompletionComparisonNaturalityFromEventFlow
              (cauchyCompletionComparisonNaturalityToEventFlow x) =
            some x) ∧
          cauchyCompletionComparisonNaturalityEncodeBHist (BHist.e0 BHist.Empty) =
            [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨cauchyCompletionComparisonNaturalityBHistCarrier⟩,
      ⟨cauchyCompletionComparisonNaturalityChapterTasteGate⟩,
      cauchyCompletionComparisonNaturality_round_trip,
      rfl⟩

end BEDC.Derived.CauchyCompletionComparisonNaturalityUp
