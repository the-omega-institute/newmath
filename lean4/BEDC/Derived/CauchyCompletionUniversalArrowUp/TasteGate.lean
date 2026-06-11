import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionUniversalArrowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionUniversalArrowUp : Type where
  | mk (M R eta F Fhat Q S H C P N : BHist) : CauchyCompletionUniversalArrowUp
  deriving DecidableEq

def cauchyCompletionUniversalArrowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionUniversalArrowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionUniversalArrowEncodeBHist h

def cauchyCompletionUniversalArrowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionUniversalArrowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionUniversalArrowDecodeBHist tail)

private theorem cauchyCompletionUniversalArrowDecode_encode_bhist :
    ∀ h : BHist,
      cauchyCompletionUniversalArrowDecodeBHist
        (cauchyCompletionUniversalArrowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionUniversalArrowFields :
    CauchyCompletionUniversalArrowUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionUniversalArrowUp.mk M R eta F Fhat Q S H C P N =>
      [M, R, eta, F, Fhat, Q, S, H, C, P, N]

def cauchyCompletionUniversalArrowToEventFlow :
    CauchyCompletionUniversalArrowUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCompletionUniversalArrowFields x).map
      cauchyCompletionUniversalArrowEncodeBHist

private def cauchyCompletionUniversalArrowEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCompletionUniversalArrowEventAt index rest

def cauchyCompletionUniversalArrowFromEventFlow (ef : EventFlow) :
    Option CauchyCompletionUniversalArrowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionUniversalArrowUp.mk
      (cauchyCompletionUniversalArrowDecodeBHist (cauchyCompletionUniversalArrowEventAt 0 ef))
      (cauchyCompletionUniversalArrowDecodeBHist (cauchyCompletionUniversalArrowEventAt 1 ef))
      (cauchyCompletionUniversalArrowDecodeBHist (cauchyCompletionUniversalArrowEventAt 2 ef))
      (cauchyCompletionUniversalArrowDecodeBHist (cauchyCompletionUniversalArrowEventAt 3 ef))
      (cauchyCompletionUniversalArrowDecodeBHist (cauchyCompletionUniversalArrowEventAt 4 ef))
      (cauchyCompletionUniversalArrowDecodeBHist (cauchyCompletionUniversalArrowEventAt 5 ef))
      (cauchyCompletionUniversalArrowDecodeBHist (cauchyCompletionUniversalArrowEventAt 6 ef))
      (cauchyCompletionUniversalArrowDecodeBHist (cauchyCompletionUniversalArrowEventAt 7 ef))
      (cauchyCompletionUniversalArrowDecodeBHist (cauchyCompletionUniversalArrowEventAt 8 ef))
      (cauchyCompletionUniversalArrowDecodeBHist (cauchyCompletionUniversalArrowEventAt 9 ef))
      (cauchyCompletionUniversalArrowDecodeBHist (cauchyCompletionUniversalArrowEventAt 10 ef)))

private theorem cauchyCompletionUniversalArrow_round_trip
    (x : CauchyCompletionUniversalArrowUp) :
    cauchyCompletionUniversalArrowFromEventFlow
        (cauchyCompletionUniversalArrowToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M R eta F Fhat Q S H C P N =>
      change
        some
          (CauchyCompletionUniversalArrowUp.mk
            (cauchyCompletionUniversalArrowDecodeBHist
              (cauchyCompletionUniversalArrowEncodeBHist M))
            (cauchyCompletionUniversalArrowDecodeBHist
              (cauchyCompletionUniversalArrowEncodeBHist R))
            (cauchyCompletionUniversalArrowDecodeBHist
              (cauchyCompletionUniversalArrowEncodeBHist eta))
            (cauchyCompletionUniversalArrowDecodeBHist
              (cauchyCompletionUniversalArrowEncodeBHist F))
            (cauchyCompletionUniversalArrowDecodeBHist
              (cauchyCompletionUniversalArrowEncodeBHist Fhat))
            (cauchyCompletionUniversalArrowDecodeBHist
              (cauchyCompletionUniversalArrowEncodeBHist Q))
            (cauchyCompletionUniversalArrowDecodeBHist
              (cauchyCompletionUniversalArrowEncodeBHist S))
            (cauchyCompletionUniversalArrowDecodeBHist
              (cauchyCompletionUniversalArrowEncodeBHist H))
            (cauchyCompletionUniversalArrowDecodeBHist
              (cauchyCompletionUniversalArrowEncodeBHist C))
            (cauchyCompletionUniversalArrowDecodeBHist
              (cauchyCompletionUniversalArrowEncodeBHist P))
            (cauchyCompletionUniversalArrowDecodeBHist
              (cauchyCompletionUniversalArrowEncodeBHist N))) =
          some (CauchyCompletionUniversalArrowUp.mk M R eta F Fhat Q S H C P N)
      rw [cauchyCompletionUniversalArrowDecode_encode_bhist M,
        cauchyCompletionUniversalArrowDecode_encode_bhist R,
        cauchyCompletionUniversalArrowDecode_encode_bhist eta,
        cauchyCompletionUniversalArrowDecode_encode_bhist F,
        cauchyCompletionUniversalArrowDecode_encode_bhist Fhat,
        cauchyCompletionUniversalArrowDecode_encode_bhist Q,
        cauchyCompletionUniversalArrowDecode_encode_bhist S,
        cauchyCompletionUniversalArrowDecode_encode_bhist H,
        cauchyCompletionUniversalArrowDecode_encode_bhist C,
        cauchyCompletionUniversalArrowDecode_encode_bhist P,
        cauchyCompletionUniversalArrowDecode_encode_bhist N]

private theorem cauchyCompletionUniversalArrowToEventFlow_injective
    {x y : CauchyCompletionUniversalArrowUp} :
    cauchyCompletionUniversalArrowToEventFlow x =
      cauchyCompletionUniversalArrowToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionUniversalArrowFromEventFlow
          (cauchyCompletionUniversalArrowToEventFlow x) =
        cauchyCompletionUniversalArrowFromEventFlow
          (cauchyCompletionUniversalArrowToEventFlow y) :=
    congrArg cauchyCompletionUniversalArrowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyCompletionUniversalArrow_round_trip x).symm
      (Eq.trans hread (cauchyCompletionUniversalArrow_round_trip y)))

instance cauchyCompletionUniversalArrowBHistCarrier :
    BHistCarrier CauchyCompletionUniversalArrowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionUniversalArrowToEventFlow
  fromEventFlow := cauchyCompletionUniversalArrowFromEventFlow

instance cauchyCompletionUniversalArrowChapterTasteGate :
    ChapterTasteGate CauchyCompletionUniversalArrowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyCompletionUniversalArrowFromEventFlow
      (cauchyCompletionUniversalArrowToEventFlow x) = some x
    exact cauchyCompletionUniversalArrow_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletionUniversalArrowToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyCompletionUniversalArrowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionUniversalArrowChapterTasteGate

theorem CauchyCompletionUniversalArrowTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CauchyCompletionUniversalArrowUp) ∧
      Nonempty (ChapterTasteGate CauchyCompletionUniversalArrowUp) ∧
        (∀ h : BHist,
          cauchyCompletionUniversalArrowDecodeBHist
              (cauchyCompletionUniversalArrowEncodeBHist h) = h) ∧
          (∀ x : CauchyCompletionUniversalArrowUp,
            cauchyCompletionUniversalArrowFromEventFlow
                (cauchyCompletionUniversalArrowToEventFlow x) = some x) ∧
            cauchyCompletionUniversalArrowEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨cauchyCompletionUniversalArrowBHistCarrier⟩
  · constructor
    · exact ⟨cauchyCompletionUniversalArrowChapterTasteGate⟩
    · constructor
      · exact cauchyCompletionUniversalArrowDecode_encode_bhist
      · constructor
        · exact cauchyCompletionUniversalArrow_round_trip
        · rfl

end BEDC.Derived.CauchyCompletionUniversalArrowUp
