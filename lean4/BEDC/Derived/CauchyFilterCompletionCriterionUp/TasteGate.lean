import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyFilterCompletionCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyFilterCompletionCriterionUp : Type where
  | mk (Q B F U S D R E H C P N : BHist) : CauchyFilterCompletionCriterionUp
  deriving DecidableEq

def cauchyFilterCompletionCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyFilterCompletionCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyFilterCompletionCriterionEncodeBHist h

def cauchyFilterCompletionCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyFilterCompletionCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyFilterCompletionCriterionDecodeBHist tail)

private theorem CauchyFilterCompletionCriterionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyFilterCompletionCriterionDecodeBHist
          (cauchyFilterCompletionCriterionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyFilterCompletionCriterionFields :
    CauchyFilterCompletionCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyFilterCompletionCriterionUp.mk Q B F U S D R E H C P N =>
      [Q, B, F, U, S, D, R, E, H, C, P, N]

def cauchyFilterCompletionCriterionToEventFlow :
    CauchyFilterCompletionCriterionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (cauchyFilterCompletionCriterionFields x).map
      cauchyFilterCompletionCriterionEncodeBHist

private def cauchyFilterCompletionCriterionRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyFilterCompletionCriterionRawAt index rest

def cauchyFilterCompletionCriterionFromEventFlow
    (flow : EventFlow) : Option CauchyFilterCompletionCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyFilterCompletionCriterionUp.mk
      (cauchyFilterCompletionCriterionDecodeBHist
        (cauchyFilterCompletionCriterionRawAt 0 flow))
      (cauchyFilterCompletionCriterionDecodeBHist
        (cauchyFilterCompletionCriterionRawAt 1 flow))
      (cauchyFilterCompletionCriterionDecodeBHist
        (cauchyFilterCompletionCriterionRawAt 2 flow))
      (cauchyFilterCompletionCriterionDecodeBHist
        (cauchyFilterCompletionCriterionRawAt 3 flow))
      (cauchyFilterCompletionCriterionDecodeBHist
        (cauchyFilterCompletionCriterionRawAt 4 flow))
      (cauchyFilterCompletionCriterionDecodeBHist
        (cauchyFilterCompletionCriterionRawAt 5 flow))
      (cauchyFilterCompletionCriterionDecodeBHist
        (cauchyFilterCompletionCriterionRawAt 6 flow))
      (cauchyFilterCompletionCriterionDecodeBHist
        (cauchyFilterCompletionCriterionRawAt 7 flow))
      (cauchyFilterCompletionCriterionDecodeBHist
        (cauchyFilterCompletionCriterionRawAt 8 flow))
      (cauchyFilterCompletionCriterionDecodeBHist
        (cauchyFilterCompletionCriterionRawAt 9 flow))
      (cauchyFilterCompletionCriterionDecodeBHist
        (cauchyFilterCompletionCriterionRawAt 10 flow))
      (cauchyFilterCompletionCriterionDecodeBHist
        (cauchyFilterCompletionCriterionRawAt 11 flow)))

private theorem CauchyFilterCompletionCriterionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyFilterCompletionCriterionUp,
      cauchyFilterCompletionCriterionFromEventFlow
          (cauchyFilterCompletionCriterionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk Q B F U S D R E H C P N =>
      change
        some
          (CauchyFilterCompletionCriterionUp.mk
            (cauchyFilterCompletionCriterionDecodeBHist
              (cauchyFilterCompletionCriterionEncodeBHist Q))
            (cauchyFilterCompletionCriterionDecodeBHist
              (cauchyFilterCompletionCriterionEncodeBHist B))
            (cauchyFilterCompletionCriterionDecodeBHist
              (cauchyFilterCompletionCriterionEncodeBHist F))
            (cauchyFilterCompletionCriterionDecodeBHist
              (cauchyFilterCompletionCriterionEncodeBHist U))
            (cauchyFilterCompletionCriterionDecodeBHist
              (cauchyFilterCompletionCriterionEncodeBHist S))
            (cauchyFilterCompletionCriterionDecodeBHist
              (cauchyFilterCompletionCriterionEncodeBHist D))
            (cauchyFilterCompletionCriterionDecodeBHist
              (cauchyFilterCompletionCriterionEncodeBHist R))
            (cauchyFilterCompletionCriterionDecodeBHist
              (cauchyFilterCompletionCriterionEncodeBHist E))
            (cauchyFilterCompletionCriterionDecodeBHist
              (cauchyFilterCompletionCriterionEncodeBHist H))
            (cauchyFilterCompletionCriterionDecodeBHist
              (cauchyFilterCompletionCriterionEncodeBHist C))
            (cauchyFilterCompletionCriterionDecodeBHist
              (cauchyFilterCompletionCriterionEncodeBHist P))
            (cauchyFilterCompletionCriterionDecodeBHist
              (cauchyFilterCompletionCriterionEncodeBHist N))) =
          some (CauchyFilterCompletionCriterionUp.mk Q B F U S D R E H C P N)
      rw [CauchyFilterCompletionCriterionTasteGate_single_carrier_alignment_decode Q,
        CauchyFilterCompletionCriterionTasteGate_single_carrier_alignment_decode B,
        CauchyFilterCompletionCriterionTasteGate_single_carrier_alignment_decode F,
        CauchyFilterCompletionCriterionTasteGate_single_carrier_alignment_decode U,
        CauchyFilterCompletionCriterionTasteGate_single_carrier_alignment_decode S,
        CauchyFilterCompletionCriterionTasteGate_single_carrier_alignment_decode D,
        CauchyFilterCompletionCriterionTasteGate_single_carrier_alignment_decode R,
        CauchyFilterCompletionCriterionTasteGate_single_carrier_alignment_decode E,
        CauchyFilterCompletionCriterionTasteGate_single_carrier_alignment_decode H,
        CauchyFilterCompletionCriterionTasteGate_single_carrier_alignment_decode C,
        CauchyFilterCompletionCriterionTasteGate_single_carrier_alignment_decode P,
        CauchyFilterCompletionCriterionTasteGate_single_carrier_alignment_decode N]

private theorem cauchyFilterCompletionCriterionToEventFlow_injective
    {x y : CauchyFilterCompletionCriterionUp} :
    cauchyFilterCompletionCriterionToEventFlow x =
        cauchyFilterCompletionCriterionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyFilterCompletionCriterionFromEventFlow
          (cauchyFilterCompletionCriterionToEventFlow x) =
        cauchyFilterCompletionCriterionFromEventFlow
          (cauchyFilterCompletionCriterionToEventFlow y) :=
    congrArg cauchyFilterCompletionCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyFilterCompletionCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyFilterCompletionCriterionTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyFilterCompletionCriterionBHistCarrier :
    BHistCarrier CauchyFilterCompletionCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyFilterCompletionCriterionToEventFlow
  fromEventFlow := cauchyFilterCompletionCriterionFromEventFlow

instance cauchyFilterCompletionCriterionChapterTasteGate :
    ChapterTasteGate CauchyFilterCompletionCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyFilterCompletionCriterionFromEventFlow
          (cauchyFilterCompletionCriterionToEventFlow x) =
        some x
    exact CauchyFilterCompletionCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyFilterCompletionCriterionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyFilterCompletionCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyFilterCompletionCriterionChapterTasteGate

theorem CauchyFilterCompletionCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyFilterCompletionCriterionDecodeBHist
          (cauchyFilterCompletionCriterionEncodeBHist h) =
        h) ∧
      (∀ x : CauchyFilterCompletionCriterionUp,
        cauchyFilterCompletionCriterionFromEventFlow
            (cauchyFilterCompletionCriterionToEventFlow x) =
          some x) ∧
        (∀ x y : CauchyFilterCompletionCriterionUp,
          cauchyFilterCompletionCriterionToEventFlow x =
              cauchyFilterCompletionCriterionToEventFlow y →
            x = y) ∧
          cauchyFilterCompletionCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyFilterCompletionCriterionTasteGate_single_carrier_alignment_decode,
      CauchyFilterCompletionCriterionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => cauchyFilterCompletionCriterionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyFilterCompletionCriterionUp
