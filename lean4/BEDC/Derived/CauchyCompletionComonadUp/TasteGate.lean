import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionComonadUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionComonadUp : Type where
  | mk (M K E Q T S R D A H C P N : BHist) : CauchyCompletionComonadUp
  deriving DecidableEq

def cauchyCompletionComonadFields : CauchyCompletionComonadUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionComonadUp.mk M K E Q T S R D A H C P N =>
      [M, K, E, Q, T, S, R, D, A, H, C, P, N]

def cauchyCompletionComonadEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionComonadEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionComonadEncodeBHist h

def cauchyCompletionComonadDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionComonadDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionComonadDecodeBHist tail)

private theorem cauchyCompletionComonad_decode_encode_bhist :
    ∀ h : BHist,
      cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyCompletionComonadToEventFlow : CauchyCompletionComonadUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyCompletionComonadFields x).map cauchyCompletionComonadEncodeBHist

private def cauchyCompletionComonadEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCompletionComonadEventAtDefault index rest

def cauchyCompletionComonadFromEventFlow
    (ef : EventFlow) : Option CauchyCompletionComonadUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionComonadUp.mk
      (cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEventAtDefault 0 ef))
      (cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEventAtDefault 1 ef))
      (cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEventAtDefault 2 ef))
      (cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEventAtDefault 3 ef))
      (cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEventAtDefault 4 ef))
      (cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEventAtDefault 5 ef))
      (cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEventAtDefault 6 ef))
      (cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEventAtDefault 7 ef))
      (cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEventAtDefault 8 ef))
      (cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEventAtDefault 9 ef))
      (cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEventAtDefault 10 ef))
      (cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEventAtDefault 11 ef))
      (cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEventAtDefault 12 ef)))

private theorem cauchyCompletionComonad_round_trip :
    ∀ x : CauchyCompletionComonadUp,
      cauchyCompletionComonadFromEventFlow
        (cauchyCompletionComonadToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M K E Q T S R D A H C P N =>
      change
        some
          (CauchyCompletionComonadUp.mk
            (cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEncodeBHist M))
            (cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEncodeBHist K))
            (cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEncodeBHist E))
            (cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEncodeBHist Q))
            (cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEncodeBHist T))
            (cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEncodeBHist S))
            (cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEncodeBHist R))
            (cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEncodeBHist D))
            (cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEncodeBHist A))
            (cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEncodeBHist H))
            (cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEncodeBHist C))
            (cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEncodeBHist P))
            (cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEncodeBHist N))) =
          some (CauchyCompletionComonadUp.mk M K E Q T S R D A H C P N)
      rw [cauchyCompletionComonad_decode_encode_bhist M,
        cauchyCompletionComonad_decode_encode_bhist K,
        cauchyCompletionComonad_decode_encode_bhist E,
        cauchyCompletionComonad_decode_encode_bhist Q,
        cauchyCompletionComonad_decode_encode_bhist T,
        cauchyCompletionComonad_decode_encode_bhist S,
        cauchyCompletionComonad_decode_encode_bhist R,
        cauchyCompletionComonad_decode_encode_bhist D,
        cauchyCompletionComonad_decode_encode_bhist A,
        cauchyCompletionComonad_decode_encode_bhist H,
        cauchyCompletionComonad_decode_encode_bhist C,
        cauchyCompletionComonad_decode_encode_bhist P,
        cauchyCompletionComonad_decode_encode_bhist N]

private theorem cauchyCompletionComonadToEventFlow_injective
    {x y : CauchyCompletionComonadUp} :
    cauchyCompletionComonadToEventFlow x = cauchyCompletionComonadToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionComonadFromEventFlow (cauchyCompletionComonadToEventFlow x) =
        cauchyCompletionComonadFromEventFlow (cauchyCompletionComonadToEventFlow y) :=
    congrArg cauchyCompletionComonadFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyCompletionComonad_round_trip x).symm
      (Eq.trans hread (cauchyCompletionComonad_round_trip y)))

instance cauchyCompletionComonadBHistCarrier : BHistCarrier CauchyCompletionComonadUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionComonadToEventFlow
  fromEventFlow := cauchyCompletionComonadFromEventFlow

instance cauchyCompletionComonadChapterTasteGate :
    ChapterTasteGate CauchyCompletionComonadUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionComonadFromEventFlow (cauchyCompletionComonadToEventFlow x) =
        some x
    exact cauchyCompletionComonad_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletionComonadToEventFlow_injective heq)

theorem CauchyCompletionComonadTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompletionComonadDecodeBHist (cauchyCompletionComonadEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyCompletionComonadUp) ∧
        Nonempty (ChapterTasteGate CauchyCompletionComonadUp) ∧
          cauchyCompletionComonadEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨cauchyCompletionComonad_decode_encode_bhist,
    ⟨⟨cauchyCompletionComonadBHistCarrier⟩,
      ⟨cauchyCompletionComonadChapterTasteGate⟩,
      rfl⟩⟩

end BEDC.Derived.CauchyCompletionComonadUp
