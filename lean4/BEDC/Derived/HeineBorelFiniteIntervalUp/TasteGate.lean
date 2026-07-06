import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HeineBorelFiniteIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HeineBorelFiniteIntervalUp : Type where
  | mk (I D B C S Q T E H R P N : BHist) : HeineBorelFiniteIntervalUp
  deriving DecidableEq

def heineBorelFiniteIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: heineBorelFiniteIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: heineBorelFiniteIntervalEncodeBHist h

def heineBorelFiniteIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (heineBorelFiniteIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (heineBorelFiniteIntervalDecodeBHist tail)

private theorem HeineBorelFiniteIntervalTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      heineBorelFiniteIntervalDecodeBHist
        (heineBorelFiniteIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def heineBorelFiniteIntervalFields : HeineBorelFiniteIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HeineBorelFiniteIntervalUp.mk I D B C S Q T E H R P N =>
      [I, D, B, C, S, Q, T, E, H, R, P, N]

def heineBorelFiniteIntervalToEventFlow : HeineBorelFiniteIntervalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (heineBorelFiniteIntervalFields x).map heineBorelFiniteIntervalEncodeBHist

private def heineBorelFiniteIntervalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => heineBorelFiniteIntervalEventAtDefault index rest

def heineBorelFiniteIntervalFromEventFlow
    (ef : EventFlow) : Option HeineBorelFiniteIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HeineBorelFiniteIntervalUp.mk
      (heineBorelFiniteIntervalDecodeBHist (heineBorelFiniteIntervalEventAtDefault 0 ef))
      (heineBorelFiniteIntervalDecodeBHist (heineBorelFiniteIntervalEventAtDefault 1 ef))
      (heineBorelFiniteIntervalDecodeBHist (heineBorelFiniteIntervalEventAtDefault 2 ef))
      (heineBorelFiniteIntervalDecodeBHist (heineBorelFiniteIntervalEventAtDefault 3 ef))
      (heineBorelFiniteIntervalDecodeBHist (heineBorelFiniteIntervalEventAtDefault 4 ef))
      (heineBorelFiniteIntervalDecodeBHist (heineBorelFiniteIntervalEventAtDefault 5 ef))
      (heineBorelFiniteIntervalDecodeBHist (heineBorelFiniteIntervalEventAtDefault 6 ef))
      (heineBorelFiniteIntervalDecodeBHist (heineBorelFiniteIntervalEventAtDefault 7 ef))
      (heineBorelFiniteIntervalDecodeBHist (heineBorelFiniteIntervalEventAtDefault 8 ef))
      (heineBorelFiniteIntervalDecodeBHist (heineBorelFiniteIntervalEventAtDefault 9 ef))
      (heineBorelFiniteIntervalDecodeBHist (heineBorelFiniteIntervalEventAtDefault 10 ef))
      (heineBorelFiniteIntervalDecodeBHist (heineBorelFiniteIntervalEventAtDefault 11 ef)))

private theorem HeineBorelFiniteIntervalTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HeineBorelFiniteIntervalUp,
      heineBorelFiniteIntervalFromEventFlow
        (heineBorelFiniteIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I D B C S Q T E H R P N =>
      change
        some
          (HeineBorelFiniteIntervalUp.mk
            (heineBorelFiniteIntervalDecodeBHist (heineBorelFiniteIntervalEncodeBHist I))
            (heineBorelFiniteIntervalDecodeBHist (heineBorelFiniteIntervalEncodeBHist D))
            (heineBorelFiniteIntervalDecodeBHist (heineBorelFiniteIntervalEncodeBHist B))
            (heineBorelFiniteIntervalDecodeBHist (heineBorelFiniteIntervalEncodeBHist C))
            (heineBorelFiniteIntervalDecodeBHist (heineBorelFiniteIntervalEncodeBHist S))
            (heineBorelFiniteIntervalDecodeBHist (heineBorelFiniteIntervalEncodeBHist Q))
            (heineBorelFiniteIntervalDecodeBHist (heineBorelFiniteIntervalEncodeBHist T))
            (heineBorelFiniteIntervalDecodeBHist (heineBorelFiniteIntervalEncodeBHist E))
            (heineBorelFiniteIntervalDecodeBHist (heineBorelFiniteIntervalEncodeBHist H))
            (heineBorelFiniteIntervalDecodeBHist (heineBorelFiniteIntervalEncodeBHist R))
            (heineBorelFiniteIntervalDecodeBHist (heineBorelFiniteIntervalEncodeBHist P))
            (heineBorelFiniteIntervalDecodeBHist (heineBorelFiniteIntervalEncodeBHist N))) =
          some (HeineBorelFiniteIntervalUp.mk I D B C S Q T E H R P N)
      rw [HeineBorelFiniteIntervalTasteGate_single_carrier_alignment_decode_encode I,
        HeineBorelFiniteIntervalTasteGate_single_carrier_alignment_decode_encode D,
        HeineBorelFiniteIntervalTasteGate_single_carrier_alignment_decode_encode B,
        HeineBorelFiniteIntervalTasteGate_single_carrier_alignment_decode_encode C,
        HeineBorelFiniteIntervalTasteGate_single_carrier_alignment_decode_encode S,
        HeineBorelFiniteIntervalTasteGate_single_carrier_alignment_decode_encode Q,
        HeineBorelFiniteIntervalTasteGate_single_carrier_alignment_decode_encode T,
        HeineBorelFiniteIntervalTasteGate_single_carrier_alignment_decode_encode E,
        HeineBorelFiniteIntervalTasteGate_single_carrier_alignment_decode_encode H,
        HeineBorelFiniteIntervalTasteGate_single_carrier_alignment_decode_encode R,
        HeineBorelFiniteIntervalTasteGate_single_carrier_alignment_decode_encode P,
        HeineBorelFiniteIntervalTasteGate_single_carrier_alignment_decode_encode N]

private theorem HeineBorelFiniteIntervalTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HeineBorelFiniteIntervalUp} :
    heineBorelFiniteIntervalToEventFlow x = heineBorelFiniteIntervalToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      heineBorelFiniteIntervalFromEventFlow (heineBorelFiniteIntervalToEventFlow x) =
        heineBorelFiniteIntervalFromEventFlow (heineBorelFiniteIntervalToEventFlow y) :=
    congrArg heineBorelFiniteIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HeineBorelFiniteIntervalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HeineBorelFiniteIntervalTasteGate_single_carrier_alignment_round_trip y)))

instance heineBorelFiniteIntervalBHistCarrier : BHistCarrier HeineBorelFiniteIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := heineBorelFiniteIntervalToEventFlow
  fromEventFlow := heineBorelFiniteIntervalFromEventFlow

instance heineBorelFiniteIntervalChapterTasteGate :
    ChapterTasteGate HeineBorelFiniteIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      heineBorelFiniteIntervalFromEventFlow
          (heineBorelFiniteIntervalToEventFlow x) = some x
    exact HeineBorelFiniteIntervalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (HeineBorelFiniteIntervalTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate HeineBorelFiniteIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  heineBorelFiniteIntervalChapterTasteGate

theorem HeineBorelFiniteIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      heineBorelFiniteIntervalDecodeBHist
        (heineBorelFiniteIntervalEncodeBHist h) = h) ∧
      (∀ x : HeineBorelFiniteIntervalUp,
        heineBorelFiniteIntervalFromEventFlow
          (heineBorelFiniteIntervalToEventFlow x) = some x) ∧
        (∀ x y : HeineBorelFiniteIntervalUp,
          heineBorelFiniteIntervalToEventFlow x = heineBorelFiniteIntervalToEventFlow y →
            x = y) ∧
          heineBorelFiniteIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨HeineBorelFiniteIntervalTasteGate_single_carrier_alignment_decode_encode,
      HeineBorelFiniteIntervalTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        HeineBorelFiniteIntervalTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.HeineBorelFiniteIntervalUp
