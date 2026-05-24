import BEDC.Derived.CauchyCompletionUnitUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionUnitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionUnitUp : Type where
  | mk (X S D R E M H C P N : BHist) : CauchyCompletionUnitUp
  deriving DecidableEq

def cauchyCompletionUnitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionUnitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionUnitEncodeBHist h

def cauchyCompletionUnitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionUnitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionUnitDecodeBHist tail)

private theorem cauchyCompletionUnit_decode_encode :
    ∀ h : BHist,
      cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyCompletionUnitFields : CauchyCompletionUnitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionUnitUp.mk X S D R E M H C P N => [X, S, D, R, E, M, H, C, P, N]

def cauchyCompletionUnitToEventFlow : CauchyCompletionUnitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCompletionUnitFields x).map cauchyCompletionUnitEncodeBHist

private def cauchyCompletionUnitEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCompletionUnitEventAt index rest

def cauchyCompletionUnitFromEventFlow : EventFlow → Option CauchyCompletionUnitUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (CauchyCompletionUnitUp.mk
          (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEventAt 0 ef))
          (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEventAt 1 ef))
          (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEventAt 2 ef))
          (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEventAt 3 ef))
          (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEventAt 4 ef))
          (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEventAt 5 ef))
          (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEventAt 6 ef))
          (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEventAt 7 ef))
          (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEventAt 8 ef))
          (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEventAt 9 ef)))

private theorem cauchyCompletionUnit_round_trip (x : CauchyCompletionUnitUp) :
    cauchyCompletionUnitFromEventFlow (cauchyCompletionUnitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X S D R E M H C P N =>
      change
        some
            (CauchyCompletionUnitUp.mk
              (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEncodeBHist X))
              (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEncodeBHist S))
              (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEncodeBHist D))
              (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEncodeBHist R))
              (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEncodeBHist E))
              (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEncodeBHist M))
              (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEncodeBHist H))
              (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEncodeBHist C))
              (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEncodeBHist P))
              (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEncodeBHist N))) =
          some (CauchyCompletionUnitUp.mk X S D R E M H C P N)
      have hmk :
          CauchyCompletionUnitUp.mk
              (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEncodeBHist X))
              (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEncodeBHist S))
              (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEncodeBHist D))
              (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEncodeBHist R))
              (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEncodeBHist E))
              (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEncodeBHist M))
              (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEncodeBHist H))
              (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEncodeBHist C))
              (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEncodeBHist P))
              (cauchyCompletionUnitDecodeBHist (cauchyCompletionUnitEncodeBHist N)) =
            CauchyCompletionUnitUp.mk X S D R E M H C P N := by
        rw [cauchyCompletionUnit_decode_encode X, cauchyCompletionUnit_decode_encode S,
          cauchyCompletionUnit_decode_encode D, cauchyCompletionUnit_decode_encode R,
          cauchyCompletionUnit_decode_encode E, cauchyCompletionUnit_decode_encode M,
          cauchyCompletionUnit_decode_encode H, cauchyCompletionUnit_decode_encode C,
          cauchyCompletionUnit_decode_encode P, cauchyCompletionUnit_decode_encode N]
      exact congrArg some hmk

private theorem cauchyCompletionUnitToEventFlow_injective {x y : CauchyCompletionUnitUp} :
    cauchyCompletionUnitToEventFlow x = cauchyCompletionUnitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionUnitFromEventFlow (cauchyCompletionUnitToEventFlow x) =
        cauchyCompletionUnitFromEventFlow (cauchyCompletionUnitToEventFlow y) :=
    congrArg cauchyCompletionUnitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyCompletionUnit_round_trip x).symm
      (Eq.trans hread (cauchyCompletionUnit_round_trip y)))

instance cauchyCompletionUnitBHistCarrier : BHistCarrier CauchyCompletionUnitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionUnitToEventFlow
  fromEventFlow := cauchyCompletionUnitFromEventFlow

instance cauchyCompletionUnitChapterTasteGate : ChapterTasteGate CauchyCompletionUnitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := cauchyCompletionUnit_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletionUnitToEventFlow_injective heq)

theorem CauchyCompletionUnitTasteGate_single_carrier_alignment :
    (∀ x : CauchyCompletionUnitUp,
      cauchyCompletionUnitFromEventFlow (cauchyCompletionUnitToEventFlow x) = some x) ∧
      (∀ x w m,
        List.Mem w (cauchyCompletionUnitToEventFlow x) →
          List.Mem m w → m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cauchyCompletionUnit_round_trip
  · intro x w m hw hm
    exact event_flow_conservativity (S := cauchyCompletionUnitToEventFlow x) hw hm

end BEDC.Derived.CauchyCompletionUnitUp
