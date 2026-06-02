import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HeineBorelFiniteNetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HeineBorelFiniteNetUp : Type where
  | mk : (I F L C R D E T Q P N : BHist) -> HeineBorelFiniteNetUp

def heineBorelFiniteNetEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: heineBorelFiniteNetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: heineBorelFiniteNetEncodeBHist h

def heineBorelFiniteNetDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (heineBorelFiniteNetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (heineBorelFiniteNetDecodeBHist tail)

theorem HeineBorelFiniteNetTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      heineBorelFiniteNetDecodeBHist (heineBorelFiniteNetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def heineBorelFiniteNetFields : HeineBorelFiniteNetUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HeineBorelFiniteNetUp.mk I F L C R D E T Q P N => [I, F, L, C, R, D, E, T, Q, P, N]

def heineBorelFiniteNetToEventFlow : HeineBorelFiniteNetUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (heineBorelFiniteNetFields x).map heineBorelFiniteNetEncodeBHist

def heineBorelFiniteNetEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => heineBorelFiniteNetEventAtDefault index rest

def heineBorelFiniteNetFromEventFlow : EventFlow -> Option HeineBorelFiniteNetUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (HeineBorelFiniteNetUp.mk
          (heineBorelFiniteNetDecodeBHist (heineBorelFiniteNetEventAtDefault 0 ef))
          (heineBorelFiniteNetDecodeBHist (heineBorelFiniteNetEventAtDefault 1 ef))
          (heineBorelFiniteNetDecodeBHist (heineBorelFiniteNetEventAtDefault 2 ef))
          (heineBorelFiniteNetDecodeBHist (heineBorelFiniteNetEventAtDefault 3 ef))
          (heineBorelFiniteNetDecodeBHist (heineBorelFiniteNetEventAtDefault 4 ef))
          (heineBorelFiniteNetDecodeBHist (heineBorelFiniteNetEventAtDefault 5 ef))
          (heineBorelFiniteNetDecodeBHist (heineBorelFiniteNetEventAtDefault 6 ef))
          (heineBorelFiniteNetDecodeBHist (heineBorelFiniteNetEventAtDefault 7 ef))
          (heineBorelFiniteNetDecodeBHist (heineBorelFiniteNetEventAtDefault 8 ef))
          (heineBorelFiniteNetDecodeBHist (heineBorelFiniteNetEventAtDefault 9 ef))
          (heineBorelFiniteNetDecodeBHist (heineBorelFiniteNetEventAtDefault 10 ef)))

theorem HeineBorelFiniteNetTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HeineBorelFiniteNetUp,
      heineBorelFiniteNetFromEventFlow (heineBorelFiniteNetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I F L C R D E T Q P N =>
      change
        some
          (HeineBorelFiniteNetUp.mk
            (heineBorelFiniteNetDecodeBHist (heineBorelFiniteNetEncodeBHist I))
            (heineBorelFiniteNetDecodeBHist (heineBorelFiniteNetEncodeBHist F))
            (heineBorelFiniteNetDecodeBHist (heineBorelFiniteNetEncodeBHist L))
            (heineBorelFiniteNetDecodeBHist (heineBorelFiniteNetEncodeBHist C))
            (heineBorelFiniteNetDecodeBHist (heineBorelFiniteNetEncodeBHist R))
            (heineBorelFiniteNetDecodeBHist (heineBorelFiniteNetEncodeBHist D))
            (heineBorelFiniteNetDecodeBHist (heineBorelFiniteNetEncodeBHist E))
            (heineBorelFiniteNetDecodeBHist (heineBorelFiniteNetEncodeBHist T))
            (heineBorelFiniteNetDecodeBHist (heineBorelFiniteNetEncodeBHist Q))
            (heineBorelFiniteNetDecodeBHist (heineBorelFiniteNetEncodeBHist P))
            (heineBorelFiniteNetDecodeBHist (heineBorelFiniteNetEncodeBHist N))) =
          some (HeineBorelFiniteNetUp.mk I F L C R D E T Q P N)
      rw [HeineBorelFiniteNetTasteGate_single_carrier_alignment_decode I,
        HeineBorelFiniteNetTasteGate_single_carrier_alignment_decode F,
        HeineBorelFiniteNetTasteGate_single_carrier_alignment_decode L,
        HeineBorelFiniteNetTasteGate_single_carrier_alignment_decode C,
        HeineBorelFiniteNetTasteGate_single_carrier_alignment_decode R,
        HeineBorelFiniteNetTasteGate_single_carrier_alignment_decode D,
        HeineBorelFiniteNetTasteGate_single_carrier_alignment_decode E,
        HeineBorelFiniteNetTasteGate_single_carrier_alignment_decode T,
        HeineBorelFiniteNetTasteGate_single_carrier_alignment_decode Q,
        HeineBorelFiniteNetTasteGate_single_carrier_alignment_decode P,
        HeineBorelFiniteNetTasteGate_single_carrier_alignment_decode N]

theorem HeineBorelFiniteNetTasteGate_single_carrier_alignment_injective
    {x y : HeineBorelFiniteNetUp} :
    heineBorelFiniteNetToEventFlow x = heineBorelFiniteNetToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      heineBorelFiniteNetFromEventFlow (heineBorelFiniteNetToEventFlow x) =
        heineBorelFiniteNetFromEventFlow (heineBorelFiniteNetToEventFlow y) :=
    congrArg heineBorelFiniteNetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HeineBorelFiniteNetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HeineBorelFiniteNetTasteGate_single_carrier_alignment_round_trip y)))

instance heineBorelFiniteNetBHistCarrier : BHistCarrier HeineBorelFiniteNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := heineBorelFiniteNetToEventFlow
  fromEventFlow := heineBorelFiniteNetFromEventFlow

instance heineBorelFiniteNetChapterTasteGate : ChapterTasteGate HeineBorelFiniteNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x => HeineBorelFiniteNetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HeineBorelFiniteNetTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate HeineBorelFiniteNetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  heineBorelFiniteNetChapterTasteGate

theorem HeineBorelFiniteNetTasteGate_single_carrier_alignment :
    (∀ h : BHist, heineBorelFiniteNetDecodeBHist (heineBorelFiniteNetEncodeBHist h) = h) ∧
      (∀ x : HeineBorelFiniteNetUp,
        heineBorelFiniteNetFromEventFlow (heineBorelFiniteNetToEventFlow x) = some x) ∧
        (∀ x y : HeineBorelFiniteNetUp,
          heineBorelFiniteNetToEventFlow x = heineBorelFiniteNetToEventFlow y -> x = y) ∧
          heineBorelFiniteNetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact HeineBorelFiniteNetTasteGate_single_carrier_alignment_decode
  · constructor
    · exact HeineBorelFiniteNetTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact HeineBorelFiniteNetTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.HeineBorelFiniteNetUp
