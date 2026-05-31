import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionOperatorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionOperatorUp : Type where
  | mk (M B U S R D Q E H C P N : BHist) : CauchyCompletionOperatorUp
  deriving DecidableEq

def cauchyCompletionOperatorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionOperatorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionOperatorEncodeBHist h

def cauchyCompletionOperatorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionOperatorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionOperatorDecodeBHist tail)

private theorem CauchyCompletionOperatorTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyCompletionOperatorDecodeBHist (cauchyCompletionOperatorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem CauchyCompletionOperatorTasteGate_single_carrier_alignment_encode_decode :
    ∀ raw : List BMark,
      cauchyCompletionOperatorEncodeBHist (cauchyCompletionOperatorDecodeBHist raw) =
        raw := by
  -- BEDC touchpoint anchor: BHist BMark
  intro raw
  induction raw with
  | nil => rfl
  | cons mark tail ih =>
      cases mark with
      | b0 => exact congrArg (List.cons BMark.b0) ih
      | b1 => exact congrArg (List.cons BMark.b1) ih

def cauchyCompletionOperatorFields :
    CauchyCompletionOperatorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionOperatorUp.mk M B U S R D Q E H C P N =>
      [M, B, U, S, R, D, Q, E, H, C, P, N]

def cauchyCompletionOperatorToEventFlow :
    CauchyCompletionOperatorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (cauchyCompletionOperatorFields x).map cauchyCompletionOperatorEncodeBHist

private def cauchyCompletionOperatorEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyCompletionOperatorEventAtDefault index rest

def cauchyCompletionOperatorFromEventFlow
    (ef : EventFlow) : Option CauchyCompletionOperatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionOperatorUp.mk
      (cauchyCompletionOperatorDecodeBHist
        (cauchyCompletionOperatorEventAtDefault 0 ef))
      (cauchyCompletionOperatorDecodeBHist
        (cauchyCompletionOperatorEventAtDefault 1 ef))
      (cauchyCompletionOperatorDecodeBHist
        (cauchyCompletionOperatorEventAtDefault 2 ef))
      (cauchyCompletionOperatorDecodeBHist
        (cauchyCompletionOperatorEventAtDefault 3 ef))
      (cauchyCompletionOperatorDecodeBHist
        (cauchyCompletionOperatorEventAtDefault 4 ef))
      (cauchyCompletionOperatorDecodeBHist
        (cauchyCompletionOperatorEventAtDefault 5 ef))
      (cauchyCompletionOperatorDecodeBHist
        (cauchyCompletionOperatorEventAtDefault 6 ef))
      (cauchyCompletionOperatorDecodeBHist
        (cauchyCompletionOperatorEventAtDefault 7 ef))
      (cauchyCompletionOperatorDecodeBHist
        (cauchyCompletionOperatorEventAtDefault 8 ef))
      (cauchyCompletionOperatorDecodeBHist
        (cauchyCompletionOperatorEventAtDefault 9 ef))
      (cauchyCompletionOperatorDecodeBHist
        (cauchyCompletionOperatorEventAtDefault 10 ef))
      (cauchyCompletionOperatorDecodeBHist
        (cauchyCompletionOperatorEventAtDefault 11 ef)))

private theorem CauchyCompletionOperatorTasteGate_single_carrier_alignment_round_trip
    (x : CauchyCompletionOperatorUp) :
    cauchyCompletionOperatorFromEventFlow
      (cauchyCompletionOperatorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M B U S R D Q E H C P N =>
      change
        some
          (CauchyCompletionOperatorUp.mk
            (cauchyCompletionOperatorDecodeBHist
              (cauchyCompletionOperatorEncodeBHist M))
            (cauchyCompletionOperatorDecodeBHist
              (cauchyCompletionOperatorEncodeBHist B))
            (cauchyCompletionOperatorDecodeBHist
              (cauchyCompletionOperatorEncodeBHist U))
            (cauchyCompletionOperatorDecodeBHist
              (cauchyCompletionOperatorEncodeBHist S))
            (cauchyCompletionOperatorDecodeBHist
              (cauchyCompletionOperatorEncodeBHist R))
            (cauchyCompletionOperatorDecodeBHist
              (cauchyCompletionOperatorEncodeBHist D))
            (cauchyCompletionOperatorDecodeBHist
              (cauchyCompletionOperatorEncodeBHist Q))
            (cauchyCompletionOperatorDecodeBHist
              (cauchyCompletionOperatorEncodeBHist E))
            (cauchyCompletionOperatorDecodeBHist
              (cauchyCompletionOperatorEncodeBHist H))
            (cauchyCompletionOperatorDecodeBHist
              (cauchyCompletionOperatorEncodeBHist C))
            (cauchyCompletionOperatorDecodeBHist
              (cauchyCompletionOperatorEncodeBHist P))
            (cauchyCompletionOperatorDecodeBHist
              (cauchyCompletionOperatorEncodeBHist N))) =
          some (CauchyCompletionOperatorUp.mk M B U S R D Q E H C P N)
      rw [CauchyCompletionOperatorTasteGate_single_carrier_alignment_decode_encode M,
        CauchyCompletionOperatorTasteGate_single_carrier_alignment_decode_encode B,
        CauchyCompletionOperatorTasteGate_single_carrier_alignment_decode_encode U,
        CauchyCompletionOperatorTasteGate_single_carrier_alignment_decode_encode S,
        CauchyCompletionOperatorTasteGate_single_carrier_alignment_decode_encode R,
        CauchyCompletionOperatorTasteGate_single_carrier_alignment_decode_encode D,
        CauchyCompletionOperatorTasteGate_single_carrier_alignment_decode_encode Q,
        CauchyCompletionOperatorTasteGate_single_carrier_alignment_decode_encode E,
        CauchyCompletionOperatorTasteGate_single_carrier_alignment_decode_encode H,
        CauchyCompletionOperatorTasteGate_single_carrier_alignment_decode_encode C,
        CauchyCompletionOperatorTasteGate_single_carrier_alignment_decode_encode P,
        CauchyCompletionOperatorTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyCompletionOperatorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletionOperatorUp} :
    cauchyCompletionOperatorToEventFlow x =
      cauchyCompletionOperatorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionOperatorFromEventFlow (cauchyCompletionOperatorToEventFlow x) =
        cauchyCompletionOperatorFromEventFlow (cauchyCompletionOperatorToEventFlow y) :=
    congrArg cauchyCompletionOperatorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletionOperatorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionOperatorTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyCompletionOperatorBHistCarrier :
    BHistCarrier CauchyCompletionOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionOperatorToEventFlow
  fromEventFlow := cauchyCompletionOperatorFromEventFlow

instance cauchyCompletionOperatorChapterTasteGate :
    ChapterTasteGate CauchyCompletionOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionOperatorFromEventFlow
        (cauchyCompletionOperatorToEventFlow x) = some x
    exact CauchyCompletionOperatorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletionOperatorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyCompletionOperatorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompletionOperatorDecodeBHist (cauchyCompletionOperatorEncodeBHist h) = h) ∧
      (∀ raw : List BMark,
        cauchyCompletionOperatorEncodeBHist
          (cauchyCompletionOperatorDecodeBHist raw) = raw) ∧
        Nonempty (BHistCarrier CauchyCompletionOperatorUp) ∧
          Nonempty (ChapterTasteGate CauchyCompletionOperatorUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyCompletionOperatorTasteGate_single_carrier_alignment_decode_encode,
      CauchyCompletionOperatorTasteGate_single_carrier_alignment_encode_decode,
      ⟨cauchyCompletionOperatorBHistCarrier⟩,
      ⟨cauchyCompletionOperatorChapterTasteGate⟩⟩

end BEDC.Derived.CauchyCompletionOperatorUp
