import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LebesgueNumberFiniteNetUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LebesgueNumberFiniteNetUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (X U delta E P C D T H R S N : BHist) : LebesgueNumberFiniteNetUp
  deriving DecidableEq

def lebesgueNumberFiniteNetEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lebesgueNumberFiniteNetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lebesgueNumberFiniteNetEncodeBHist h

def lebesgueNumberFiniteNetDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lebesgueNumberFiniteNetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lebesgueNumberFiniteNetDecodeBHist tail)

private theorem lebesgueNumberFiniteNetDecode_encode :
    ∀ h : BHist, lebesgueNumberFiniteNetDecodeBHist
      (lebesgueNumberFiniteNetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lebesgueNumberFiniteNetFields : LebesgueNumberFiniteNetUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LebesgueNumberFiniteNetUp.mk X U delta E P C D T H R S N =>
      [X, U, delta, E, P, C, D, T, H, R, S, N]

def lebesgueNumberFiniteNetToEventFlow : LebesgueNumberFiniteNetUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (lebesgueNumberFiniteNetFields x).map lebesgueNumberFiniteNetEncodeBHist

private def lebesgueNumberFiniteNetEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lebesgueNumberFiniteNetEventAt index rest

def lebesgueNumberFiniteNetFromEventFlow (ef : EventFlow) :
    Option LebesgueNumberFiniteNetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LebesgueNumberFiniteNetUp.mk
      (lebesgueNumberFiniteNetDecodeBHist (lebesgueNumberFiniteNetEventAt 0 ef))
      (lebesgueNumberFiniteNetDecodeBHist (lebesgueNumberFiniteNetEventAt 1 ef))
      (lebesgueNumberFiniteNetDecodeBHist (lebesgueNumberFiniteNetEventAt 2 ef))
      (lebesgueNumberFiniteNetDecodeBHist (lebesgueNumberFiniteNetEventAt 3 ef))
      (lebesgueNumberFiniteNetDecodeBHist (lebesgueNumberFiniteNetEventAt 4 ef))
      (lebesgueNumberFiniteNetDecodeBHist (lebesgueNumberFiniteNetEventAt 5 ef))
      (lebesgueNumberFiniteNetDecodeBHist (lebesgueNumberFiniteNetEventAt 6 ef))
      (lebesgueNumberFiniteNetDecodeBHist (lebesgueNumberFiniteNetEventAt 7 ef))
      (lebesgueNumberFiniteNetDecodeBHist (lebesgueNumberFiniteNetEventAt 8 ef))
      (lebesgueNumberFiniteNetDecodeBHist (lebesgueNumberFiniteNetEventAt 9 ef))
      (lebesgueNumberFiniteNetDecodeBHist (lebesgueNumberFiniteNetEventAt 10 ef))
      (lebesgueNumberFiniteNetDecodeBHist (lebesgueNumberFiniteNetEventAt 11 ef)))

private theorem lebesgueNumberFiniteNet_round_trip :
    ∀ x : LebesgueNumberFiniteNetUp,
      lebesgueNumberFiniteNetFromEventFlow (lebesgueNumberFiniteNetToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X U delta E P C D T H R S N =>
      change
        some
          (LebesgueNumberFiniteNetUp.mk
            (lebesgueNumberFiniteNetDecodeBHist (lebesgueNumberFiniteNetEncodeBHist X))
            (lebesgueNumberFiniteNetDecodeBHist (lebesgueNumberFiniteNetEncodeBHist U))
            (lebesgueNumberFiniteNetDecodeBHist (lebesgueNumberFiniteNetEncodeBHist delta))
            (lebesgueNumberFiniteNetDecodeBHist (lebesgueNumberFiniteNetEncodeBHist E))
            (lebesgueNumberFiniteNetDecodeBHist (lebesgueNumberFiniteNetEncodeBHist P))
            (lebesgueNumberFiniteNetDecodeBHist (lebesgueNumberFiniteNetEncodeBHist C))
            (lebesgueNumberFiniteNetDecodeBHist (lebesgueNumberFiniteNetEncodeBHist D))
            (lebesgueNumberFiniteNetDecodeBHist (lebesgueNumberFiniteNetEncodeBHist T))
            (lebesgueNumberFiniteNetDecodeBHist (lebesgueNumberFiniteNetEncodeBHist H))
            (lebesgueNumberFiniteNetDecodeBHist (lebesgueNumberFiniteNetEncodeBHist R))
            (lebesgueNumberFiniteNetDecodeBHist (lebesgueNumberFiniteNetEncodeBHist S))
            (lebesgueNumberFiniteNetDecodeBHist (lebesgueNumberFiniteNetEncodeBHist N))) =
          some (LebesgueNumberFiniteNetUp.mk X U delta E P C D T H R S N)
      rw [lebesgueNumberFiniteNetDecode_encode X, lebesgueNumberFiniteNetDecode_encode U,
        lebesgueNumberFiniteNetDecode_encode delta, lebesgueNumberFiniteNetDecode_encode E,
        lebesgueNumberFiniteNetDecode_encode P, lebesgueNumberFiniteNetDecode_encode C,
        lebesgueNumberFiniteNetDecode_encode D, lebesgueNumberFiniteNetDecode_encode T,
        lebesgueNumberFiniteNetDecode_encode H, lebesgueNumberFiniteNetDecode_encode R,
        lebesgueNumberFiniteNetDecode_encode S, lebesgueNumberFiniteNetDecode_encode N]

private theorem lebesgueNumberFiniteNetToEventFlow_injective
    {x y : LebesgueNumberFiniteNetUp} :
    lebesgueNumberFiniteNetToEventFlow x = lebesgueNumberFiniteNetToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lebesgueNumberFiniteNetFromEventFlow (lebesgueNumberFiniteNetToEventFlow x) =
        lebesgueNumberFiniteNetFromEventFlow (lebesgueNumberFiniteNetToEventFlow y) :=
    congrArg lebesgueNumberFiniteNetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (lebesgueNumberFiniteNet_round_trip x).symm
      (Eq.trans hread (lebesgueNumberFiniteNet_round_trip y)))

instance lebesgueNumberFiniteNetBHistCarrier : BHistCarrier LebesgueNumberFiniteNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lebesgueNumberFiniteNetToEventFlow
  fromEventFlow := lebesgueNumberFiniteNetFromEventFlow

instance lebesgueNumberFiniteNetChapterTasteGate :
    ChapterTasteGate LebesgueNumberFiniteNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      lebesgueNumberFiniteNetFromEventFlow (lebesgueNumberFiniteNetToEventFlow x) = some x
    exact lebesgueNumberFiniteNet_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (lebesgueNumberFiniteNetToEventFlow_injective heq)

theorem LebesgueNumberFiniteNetTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier LebesgueNumberFiniteNetUp) ∧
      Nonempty (ChapterTasteGate LebesgueNumberFiniteNetUp) ∧
        (∀ h : BHist,
          lebesgueNumberFiniteNetDecodeBHist (lebesgueNumberFiniteNetEncodeBHist h) = h) ∧
          (∀ x : LebesgueNumberFiniteNetUp,
            lebesgueNumberFiniteNetFromEventFlow (lebesgueNumberFiniteNetToEventFlow x) =
              some x) ∧
            (∀ x y : LebesgueNumberFiniteNetUp,
              BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y -> x = y) ∧
              lebesgueNumberFiniteNetEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  refine
    ⟨⟨lebesgueNumberFiniteNetBHistCarrier⟩,
      ⟨lebesgueNumberFiniteNetChapterTasteGate⟩,
      lebesgueNumberFiniteNetDecode_encode,
      lebesgueNumberFiniteNet_round_trip,
      ?_,
      rfl⟩
  intro x y heq
  change lebesgueNumberFiniteNetToEventFlow x = lebesgueNumberFiniteNetToEventFlow y at heq
  exact lebesgueNumberFiniteNetToEventFlow_injective heq

end BEDC.Derived.LebesgueNumberFiniteNetUp.TasteGate
