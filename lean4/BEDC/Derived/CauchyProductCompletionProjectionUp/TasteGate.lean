import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyProductCompletionProjectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyProductCompletionProjectionUp : Type where
  | mk
      (Q pi0 pi1 S0 S1 D0 D1 R0 R1 L0 L1 H C P N : BHist) :
      CauchyProductCompletionProjectionUp
  deriving DecidableEq

def cauchyProductCompletionProjectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyProductCompletionProjectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyProductCompletionProjectionEncodeBHist h

def cauchyProductCompletionProjectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyProductCompletionProjectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyProductCompletionProjectionDecodeBHist tail)

private theorem cauchyProductCompletionProjectionDecodeEncode :
    ∀ h : BHist,
      cauchyProductCompletionProjectionDecodeBHist
        (cauchyProductCompletionProjectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyProductCompletionProjectionFields :
    CauchyProductCompletionProjectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyProductCompletionProjectionUp.mk
      Q pi0 pi1 S0 S1 D0 D1 R0 R1 L0 L1 H C P N =>
      [Q, pi0, pi1, S0, S1, D0, D1, R0, R1, L0, L1, H, C, P, N]

def cauchyProductCompletionProjectionToEventFlow :
    CauchyProductCompletionProjectionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (cauchyProductCompletionProjectionFields x).map
      cauchyProductCompletionProjectionEncodeBHist

private def cauchyProductCompletionProjectionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyProductCompletionProjectionEventAtDefault index rest

def cauchyProductCompletionProjectionFromEventFlow
    (ef : EventFlow) : Option CauchyProductCompletionProjectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyProductCompletionProjectionUp.mk
      (cauchyProductCompletionProjectionDecodeBHist
        (cauchyProductCompletionProjectionEventAtDefault 0 ef))
      (cauchyProductCompletionProjectionDecodeBHist
        (cauchyProductCompletionProjectionEventAtDefault 1 ef))
      (cauchyProductCompletionProjectionDecodeBHist
        (cauchyProductCompletionProjectionEventAtDefault 2 ef))
      (cauchyProductCompletionProjectionDecodeBHist
        (cauchyProductCompletionProjectionEventAtDefault 3 ef))
      (cauchyProductCompletionProjectionDecodeBHist
        (cauchyProductCompletionProjectionEventAtDefault 4 ef))
      (cauchyProductCompletionProjectionDecodeBHist
        (cauchyProductCompletionProjectionEventAtDefault 5 ef))
      (cauchyProductCompletionProjectionDecodeBHist
        (cauchyProductCompletionProjectionEventAtDefault 6 ef))
      (cauchyProductCompletionProjectionDecodeBHist
        (cauchyProductCompletionProjectionEventAtDefault 7 ef))
      (cauchyProductCompletionProjectionDecodeBHist
        (cauchyProductCompletionProjectionEventAtDefault 8 ef))
      (cauchyProductCompletionProjectionDecodeBHist
        (cauchyProductCompletionProjectionEventAtDefault 9 ef))
      (cauchyProductCompletionProjectionDecodeBHist
        (cauchyProductCompletionProjectionEventAtDefault 10 ef))
      (cauchyProductCompletionProjectionDecodeBHist
        (cauchyProductCompletionProjectionEventAtDefault 11 ef))
      (cauchyProductCompletionProjectionDecodeBHist
        (cauchyProductCompletionProjectionEventAtDefault 12 ef))
      (cauchyProductCompletionProjectionDecodeBHist
        (cauchyProductCompletionProjectionEventAtDefault 13 ef))
      (cauchyProductCompletionProjectionDecodeBHist
        (cauchyProductCompletionProjectionEventAtDefault 14 ef)))

private theorem cauchyProductCompletionProjectionRoundTrip :
    ∀ x : CauchyProductCompletionProjectionUp,
      cauchyProductCompletionProjectionFromEventFlow
        (cauchyProductCompletionProjectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q pi0 pi1 S0 S1 D0 D1 R0 R1 L0 L1 H C P N =>
      change
        some
          (CauchyProductCompletionProjectionUp.mk
            (cauchyProductCompletionProjectionDecodeBHist
              (cauchyProductCompletionProjectionEncodeBHist Q))
            (cauchyProductCompletionProjectionDecodeBHist
              (cauchyProductCompletionProjectionEncodeBHist pi0))
            (cauchyProductCompletionProjectionDecodeBHist
              (cauchyProductCompletionProjectionEncodeBHist pi1))
            (cauchyProductCompletionProjectionDecodeBHist
              (cauchyProductCompletionProjectionEncodeBHist S0))
            (cauchyProductCompletionProjectionDecodeBHist
              (cauchyProductCompletionProjectionEncodeBHist S1))
            (cauchyProductCompletionProjectionDecodeBHist
              (cauchyProductCompletionProjectionEncodeBHist D0))
            (cauchyProductCompletionProjectionDecodeBHist
              (cauchyProductCompletionProjectionEncodeBHist D1))
            (cauchyProductCompletionProjectionDecodeBHist
              (cauchyProductCompletionProjectionEncodeBHist R0))
            (cauchyProductCompletionProjectionDecodeBHist
              (cauchyProductCompletionProjectionEncodeBHist R1))
            (cauchyProductCompletionProjectionDecodeBHist
              (cauchyProductCompletionProjectionEncodeBHist L0))
            (cauchyProductCompletionProjectionDecodeBHist
              (cauchyProductCompletionProjectionEncodeBHist L1))
            (cauchyProductCompletionProjectionDecodeBHist
              (cauchyProductCompletionProjectionEncodeBHist H))
            (cauchyProductCompletionProjectionDecodeBHist
              (cauchyProductCompletionProjectionEncodeBHist C))
            (cauchyProductCompletionProjectionDecodeBHist
              (cauchyProductCompletionProjectionEncodeBHist P))
            (cauchyProductCompletionProjectionDecodeBHist
              (cauchyProductCompletionProjectionEncodeBHist N))) =
          some
            (CauchyProductCompletionProjectionUp.mk
              Q pi0 pi1 S0 S1 D0 D1 R0 R1 L0 L1 H C P N)
      rw [cauchyProductCompletionProjectionDecodeEncode Q,
        cauchyProductCompletionProjectionDecodeEncode pi0,
        cauchyProductCompletionProjectionDecodeEncode pi1,
        cauchyProductCompletionProjectionDecodeEncode S0,
        cauchyProductCompletionProjectionDecodeEncode S1,
        cauchyProductCompletionProjectionDecodeEncode D0,
        cauchyProductCompletionProjectionDecodeEncode D1,
        cauchyProductCompletionProjectionDecodeEncode R0,
        cauchyProductCompletionProjectionDecodeEncode R1,
        cauchyProductCompletionProjectionDecodeEncode L0,
        cauchyProductCompletionProjectionDecodeEncode L1,
        cauchyProductCompletionProjectionDecodeEncode H,
        cauchyProductCompletionProjectionDecodeEncode C,
        cauchyProductCompletionProjectionDecodeEncode P,
        cauchyProductCompletionProjectionDecodeEncode N]

private theorem cauchyProductCompletionProjectionToEventFlow_injective
    {x y : CauchyProductCompletionProjectionUp} :
    cauchyProductCompletionProjectionToEventFlow x =
      cauchyProductCompletionProjectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyProductCompletionProjectionFromEventFlow
          (cauchyProductCompletionProjectionToEventFlow x) =
        cauchyProductCompletionProjectionFromEventFlow
          (cauchyProductCompletionProjectionToEventFlow y) :=
    congrArg cauchyProductCompletionProjectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyProductCompletionProjectionRoundTrip x).symm
      (Eq.trans hread (cauchyProductCompletionProjectionRoundTrip y)))

instance cauchyProductCompletionProjectionBHistCarrier :
    BHistCarrier CauchyProductCompletionProjectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyProductCompletionProjectionToEventFlow
  fromEventFlow := cauchyProductCompletionProjectionFromEventFlow

instance cauchyProductCompletionProjectionChapterTasteGate :
    ChapterTasteGate CauchyProductCompletionProjectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyProductCompletionProjectionFromEventFlow
          (cauchyProductCompletionProjectionToEventFlow x) = some x
    exact cauchyProductCompletionProjectionRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyProductCompletionProjectionToEventFlow_injective heq)

theorem CauchyProductCompletionProjectionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyProductCompletionProjectionDecodeBHist
        (cauchyProductCompletionProjectionEncodeBHist h) = h) ∧
      (∀ x : CauchyProductCompletionProjectionUp,
        cauchyProductCompletionProjectionFromEventFlow
          (cauchyProductCompletionProjectionToEventFlow x) = some x) ∧
        cauchyProductCompletionProjectionEncodeBHist BHist.Empty = ([] : List BMark) ∧
          Nonempty (ChapterTasteGate CauchyProductCompletionProjectionUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨cauchyProductCompletionProjectionDecodeEncode,
      cauchyProductCompletionProjectionRoundTrip,
      rfl,
      ⟨cauchyProductCompletionProjectionChapterTasteGate⟩⟩

end BEDC.Derived.CauchyProductCompletionProjectionUp
