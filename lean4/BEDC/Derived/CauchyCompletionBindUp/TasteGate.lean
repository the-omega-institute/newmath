import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionBindUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionBindUp : Type where
  | mk (S U K E H C P N : BHist) : CauchyCompletionBindUp
  deriving DecidableEq

def cauchyCompletionBindFields : CauchyCompletionBindUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionBindUp.mk S U K E H C P N => [S, U, K, E, H, C, P, N]

def cauchyCompletionBindEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionBindEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionBindEncodeBHist h

def cauchyCompletionBindDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionBindDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionBindDecodeBHist tail)

private theorem cauchyCompletionBind_decode_encode_bhist :
    ∀ h : BHist, cauchyCompletionBindDecodeBHist (cauchyCompletionBindEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyCompletionBindToEventFlow : CauchyCompletionBindUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyCompletionBindFields x).map cauchyCompletionBindEncodeBHist

private def cauchyCompletionBindEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCompletionBindEventAtDefault index rest

def cauchyCompletionBindFromEventFlow (ef : EventFlow) : Option CauchyCompletionBindUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionBindUp.mk
      (cauchyCompletionBindDecodeBHist (cauchyCompletionBindEventAtDefault 0 ef))
      (cauchyCompletionBindDecodeBHist (cauchyCompletionBindEventAtDefault 1 ef))
      (cauchyCompletionBindDecodeBHist (cauchyCompletionBindEventAtDefault 2 ef))
      (cauchyCompletionBindDecodeBHist (cauchyCompletionBindEventAtDefault 3 ef))
      (cauchyCompletionBindDecodeBHist (cauchyCompletionBindEventAtDefault 4 ef))
      (cauchyCompletionBindDecodeBHist (cauchyCompletionBindEventAtDefault 5 ef))
      (cauchyCompletionBindDecodeBHist (cauchyCompletionBindEventAtDefault 6 ef))
      (cauchyCompletionBindDecodeBHist (cauchyCompletionBindEventAtDefault 7 ef)))

private theorem cauchyCompletionBind_round_trip :
    ∀ x : CauchyCompletionBindUp,
      cauchyCompletionBindFromEventFlow (cauchyCompletionBindToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S U K E H C P N =>
      change
        some
          (CauchyCompletionBindUp.mk
            (cauchyCompletionBindDecodeBHist (cauchyCompletionBindEncodeBHist S))
            (cauchyCompletionBindDecodeBHist (cauchyCompletionBindEncodeBHist U))
            (cauchyCompletionBindDecodeBHist (cauchyCompletionBindEncodeBHist K))
            (cauchyCompletionBindDecodeBHist (cauchyCompletionBindEncodeBHist E))
            (cauchyCompletionBindDecodeBHist (cauchyCompletionBindEncodeBHist H))
            (cauchyCompletionBindDecodeBHist (cauchyCompletionBindEncodeBHist C))
            (cauchyCompletionBindDecodeBHist (cauchyCompletionBindEncodeBHist P))
            (cauchyCompletionBindDecodeBHist (cauchyCompletionBindEncodeBHist N))) =
          some (CauchyCompletionBindUp.mk S U K E H C P N)
      rw [cauchyCompletionBind_decode_encode_bhist S,
        cauchyCompletionBind_decode_encode_bhist U,
        cauchyCompletionBind_decode_encode_bhist K,
        cauchyCompletionBind_decode_encode_bhist E,
        cauchyCompletionBind_decode_encode_bhist H,
        cauchyCompletionBind_decode_encode_bhist C,
        cauchyCompletionBind_decode_encode_bhist P,
        cauchyCompletionBind_decode_encode_bhist N]

private theorem cauchyCompletionBindToEventFlow_injective
    {x y : CauchyCompletionBindUp} :
    cauchyCompletionBindToEventFlow x = cauchyCompletionBindToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionBindFromEventFlow (cauchyCompletionBindToEventFlow x) =
        cauchyCompletionBindFromEventFlow (cauchyCompletionBindToEventFlow y) :=
    congrArg cauchyCompletionBindFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyCompletionBind_round_trip x).symm
      (Eq.trans hread (cauchyCompletionBind_round_trip y)))

instance cauchyCompletionBindBHistCarrier : BHistCarrier CauchyCompletionBindUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionBindToEventFlow
  fromEventFlow := cauchyCompletionBindFromEventFlow

instance cauchyCompletionBindChapterTasteGate : ChapterTasteGate CauchyCompletionBindUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyCompletionBindFromEventFlow (cauchyCompletionBindToEventFlow x) = some x
    exact cauchyCompletionBind_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletionBindToEventFlow_injective heq)

theorem CauchyCompletionBindTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyCompletionBindDecodeBHist (cauchyCompletionBindEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyCompletionBindUp) ∧
        Nonempty (ChapterTasteGate CauchyCompletionBindUp) ∧
          cauchyCompletionBindEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨cauchyCompletionBind_decode_encode_bhist,
    ⟨⟨cauchyCompletionBindBHistCarrier⟩,
      ⟨cauchyCompletionBindChapterTasteGate⟩,
      rfl⟩⟩

end BEDC.Derived.CauchyCompletionBindUp
