import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HeineBorelIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HeineBorelIntervalUp : Type where
  | mk : (A B K M Z F T S R E Q C P N : BHist) -> HeineBorelIntervalUp

def heineBorelIntervalEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: heineBorelIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: heineBorelIntervalEncodeBHist h

def heineBorelIntervalDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (heineBorelIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (heineBorelIntervalDecodeBHist tail)

theorem HeineBorelIntervalTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def heineBorelIntervalFields : HeineBorelIntervalUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N =>
      [A, B, K, M, Z, F, T, S, R, E, Q, C, P, N]

def heineBorelIntervalToEventFlow : HeineBorelIntervalUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (heineBorelIntervalFields x).map heineBorelIntervalEncodeBHist

def heineBorelIntervalEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => heineBorelIntervalEventAtDefault index rest

def heineBorelIntervalFromEventFlow : EventFlow -> Option HeineBorelIntervalUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (HeineBorelIntervalUp.mk
          (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 0 ef))
          (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 1 ef))
          (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 2 ef))
          (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 3 ef))
          (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 4 ef))
          (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 5 ef))
          (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 6 ef))
          (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 7 ef))
          (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 8 ef))
          (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 9 ef))
          (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 10 ef))
          (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 11 ef))
          (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 12 ef))
          (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 13 ef)))

theorem HeineBorelIntervalTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HeineBorelIntervalUp,
      heineBorelIntervalFromEventFlow (heineBorelIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B K M Z F T S R E Q C P N =>
      change
        some
          (HeineBorelIntervalUp.mk
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist A))
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist B))
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist K))
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist M))
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist Z))
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist F))
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist T))
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist S))
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist R))
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist E))
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist Q))
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist C))
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist P))
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist N))) =
          some (HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N)
      rw [HeineBorelIntervalTasteGate_single_carrier_alignment_decode A,
        HeineBorelIntervalTasteGate_single_carrier_alignment_decode B,
        HeineBorelIntervalTasteGate_single_carrier_alignment_decode K,
        HeineBorelIntervalTasteGate_single_carrier_alignment_decode M,
        HeineBorelIntervalTasteGate_single_carrier_alignment_decode Z,
        HeineBorelIntervalTasteGate_single_carrier_alignment_decode F,
        HeineBorelIntervalTasteGate_single_carrier_alignment_decode T,
        HeineBorelIntervalTasteGate_single_carrier_alignment_decode S,
        HeineBorelIntervalTasteGate_single_carrier_alignment_decode R,
        HeineBorelIntervalTasteGate_single_carrier_alignment_decode E,
        HeineBorelIntervalTasteGate_single_carrier_alignment_decode Q,
        HeineBorelIntervalTasteGate_single_carrier_alignment_decode C,
        HeineBorelIntervalTasteGate_single_carrier_alignment_decode P,
        HeineBorelIntervalTasteGate_single_carrier_alignment_decode N]

theorem HeineBorelIntervalTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HeineBorelIntervalUp} :
    heineBorelIntervalToEventFlow x = heineBorelIntervalToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      heineBorelIntervalFromEventFlow (heineBorelIntervalToEventFlow x) =
        heineBorelIntervalFromEventFlow (heineBorelIntervalToEventFlow y) :=
    congrArg heineBorelIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HeineBorelIntervalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HeineBorelIntervalTasteGate_single_carrier_alignment_round_trip y)))

instance heineBorelIntervalBHistCarrier : BHistCarrier HeineBorelIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := heineBorelIntervalToEventFlow
  fromEventFlow := heineBorelIntervalFromEventFlow

instance heineBorelIntervalChapterTasteGate : ChapterTasteGate HeineBorelIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x => HeineBorelIntervalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HeineBorelIntervalTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate HeineBorelIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  heineBorelIntervalChapterTasteGate

theorem HeineBorelIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist, heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier HeineBorelIntervalUp) ∧
        Nonempty (ChapterTasteGate HeineBorelIntervalUp) ∧
          heineBorelIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨HeineBorelIntervalTasteGate_single_carrier_alignment_decode,
      ⟨heineBorelIntervalBHistCarrier⟩,
      ⟨heineBorelIntervalChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.HeineBorelIntervalUp
