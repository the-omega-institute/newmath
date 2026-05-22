import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyFilterClusterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyFilterClusterUp : Type where
  | mk (F M U W Q S D E H C P N : BHist) : CauchyFilterClusterUp
  deriving DecidableEq

def cauchyFilterClusterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyFilterClusterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyFilterClusterEncodeBHist h

def cauchyFilterClusterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyFilterClusterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyFilterClusterDecodeBHist tail)

private theorem CauchyFilterClusterUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyFilterClusterToEventFlow : CauchyFilterClusterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyFilterClusterUp.mk F M U W Q S D E H C P N =>
      [cauchyFilterClusterEncodeBHist F,
        cauchyFilterClusterEncodeBHist M,
        cauchyFilterClusterEncodeBHist U,
        cauchyFilterClusterEncodeBHist W,
        cauchyFilterClusterEncodeBHist Q,
        cauchyFilterClusterEncodeBHist S,
        cauchyFilterClusterEncodeBHist D,
        cauchyFilterClusterEncodeBHist E,
        cauchyFilterClusterEncodeBHist H,
        cauchyFilterClusterEncodeBHist C,
        cauchyFilterClusterEncodeBHist P,
        cauchyFilterClusterEncodeBHist N]

private def cauchyFilterClusterEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyFilterClusterEventAtDefault index rest

def cauchyFilterClusterFromEventFlow (ef : EventFlow) : Option CauchyFilterClusterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyFilterClusterUp.mk
      (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEventAtDefault 0 ef))
      (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEventAtDefault 1 ef))
      (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEventAtDefault 2 ef))
      (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEventAtDefault 3 ef))
      (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEventAtDefault 4 ef))
      (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEventAtDefault 5 ef))
      (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEventAtDefault 6 ef))
      (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEventAtDefault 7 ef))
      (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEventAtDefault 8 ef))
      (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEventAtDefault 9 ef))
      (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEventAtDefault 10 ef))
      (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEventAtDefault 11 ef)))

private theorem CauchyFilterClusterUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyFilterClusterUp,
      cauchyFilterClusterFromEventFlow (cauchyFilterClusterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F M U W Q S D E H C P N =>
      change
        some
          (CauchyFilterClusterUp.mk
            (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist F))
            (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist M))
            (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist U))
            (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist W))
            (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist Q))
            (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist S))
            (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist D))
            (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist E))
            (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist H))
            (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist C))
            (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist P))
            (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist N))) =
          some (CauchyFilterClusterUp.mk F M U W Q S D E H C P N)
      rw [CauchyFilterClusterUpTasteGate_single_carrier_alignment_decode_encode F,
        CauchyFilterClusterUpTasteGate_single_carrier_alignment_decode_encode M,
        CauchyFilterClusterUpTasteGate_single_carrier_alignment_decode_encode U,
        CauchyFilterClusterUpTasteGate_single_carrier_alignment_decode_encode W,
        CauchyFilterClusterUpTasteGate_single_carrier_alignment_decode_encode Q,
        CauchyFilterClusterUpTasteGate_single_carrier_alignment_decode_encode S,
        CauchyFilterClusterUpTasteGate_single_carrier_alignment_decode_encode D,
        CauchyFilterClusterUpTasteGate_single_carrier_alignment_decode_encode E,
        CauchyFilterClusterUpTasteGate_single_carrier_alignment_decode_encode H,
        CauchyFilterClusterUpTasteGate_single_carrier_alignment_decode_encode C,
        CauchyFilterClusterUpTasteGate_single_carrier_alignment_decode_encode P,
        CauchyFilterClusterUpTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyFilterClusterUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyFilterClusterUp} :
    cauchyFilterClusterToEventFlow x = cauchyFilterClusterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyFilterClusterFromEventFlow (cauchyFilterClusterToEventFlow x) =
        cauchyFilterClusterFromEventFlow (cauchyFilterClusterToEventFlow y) :=
    congrArg cauchyFilterClusterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyFilterClusterUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyFilterClusterUpTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyFilterClusterBHistCarrier : BHistCarrier CauchyFilterClusterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyFilterClusterToEventFlow
  fromEventFlow := cauchyFilterClusterFromEventFlow

instance cauchyFilterClusterChapterTasteGate :
    ChapterTasteGate CauchyFilterClusterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyFilterClusterFromEventFlow (cauchyFilterClusterToEventFlow x) = some x
    exact CauchyFilterClusterUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyFilterClusterUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyFilterClusterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyFilterClusterChapterTasteGate

theorem CauchyFilterClusterUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist h) = h) ∧
      (∀ x : CauchyFilterClusterUp,
        cauchyFilterClusterFromEventFlow (cauchyFilterClusterToEventFlow x) = some x) ∧
        (∀ x y : CauchyFilterClusterUp,
          cauchyFilterClusterToEventFlow x = cauchyFilterClusterToEventFlow y → x = y) ∧
          cauchyFilterClusterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyFilterClusterUpTasteGate_single_carrier_alignment_decode_encode,
      CauchyFilterClusterUpTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        CauchyFilterClusterUpTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.CauchyFilterClusterUp
