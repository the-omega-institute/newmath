import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteRealSupremumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteRealSupremumUp : Type where
  | mk (R I O M U L H C P N : BHist) : FiniteRealSupremumUp
  deriving DecidableEq

def finiteRealSupremumEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteRealSupremumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteRealSupremumEncodeBHist h

def finiteRealSupremumDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteRealSupremumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteRealSupremumDecodeBHist tail)

private theorem FiniteRealSupremumTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, finiteRealSupremumDecodeBHist (finiteRealSupremumEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteRealSupremumFields : FiniteRealSupremumUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteRealSupremumUp.mk R I O M U L H C P N => [R, I, O, M, U, L, H, C, P, N]

def finiteRealSupremumToEventFlow : FiniteRealSupremumUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteRealSupremumFields x).map finiteRealSupremumEncodeBHist

private def finiteRealSupremumEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteRealSupremumEventAt index rest

def finiteRealSupremumFromEventFlow (ef : EventFlow) : Option FiniteRealSupremumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteRealSupremumUp.mk
      (finiteRealSupremumDecodeBHist (finiteRealSupremumEventAt 0 ef))
      (finiteRealSupremumDecodeBHist (finiteRealSupremumEventAt 1 ef))
      (finiteRealSupremumDecodeBHist (finiteRealSupremumEventAt 2 ef))
      (finiteRealSupremumDecodeBHist (finiteRealSupremumEventAt 3 ef))
      (finiteRealSupremumDecodeBHist (finiteRealSupremumEventAt 4 ef))
      (finiteRealSupremumDecodeBHist (finiteRealSupremumEventAt 5 ef))
      (finiteRealSupremumDecodeBHist (finiteRealSupremumEventAt 6 ef))
      (finiteRealSupremumDecodeBHist (finiteRealSupremumEventAt 7 ef))
      (finiteRealSupremumDecodeBHist (finiteRealSupremumEventAt 8 ef))
      (finiteRealSupremumDecodeBHist (finiteRealSupremumEventAt 9 ef)))

private theorem FiniteRealSupremumTasteGate_single_carrier_alignment_round_trip
    (x : FiniteRealSupremumUp) :
    finiteRealSupremumFromEventFlow (finiteRealSupremumToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk R I O M U L H C P N =>
      change
        some
          (FiniteRealSupremumUp.mk
            (finiteRealSupremumDecodeBHist (finiteRealSupremumEncodeBHist R))
            (finiteRealSupremumDecodeBHist (finiteRealSupremumEncodeBHist I))
            (finiteRealSupremumDecodeBHist (finiteRealSupremumEncodeBHist O))
            (finiteRealSupremumDecodeBHist (finiteRealSupremumEncodeBHist M))
            (finiteRealSupremumDecodeBHist (finiteRealSupremumEncodeBHist U))
            (finiteRealSupremumDecodeBHist (finiteRealSupremumEncodeBHist L))
            (finiteRealSupremumDecodeBHist (finiteRealSupremumEncodeBHist H))
            (finiteRealSupremumDecodeBHist (finiteRealSupremumEncodeBHist C))
            (finiteRealSupremumDecodeBHist (finiteRealSupremumEncodeBHist P))
            (finiteRealSupremumDecodeBHist (finiteRealSupremumEncodeBHist N))) =
          some (FiniteRealSupremumUp.mk R I O M U L H C P N)
      rw [FiniteRealSupremumTasteGate_single_carrier_alignment_decode R,
        FiniteRealSupremumTasteGate_single_carrier_alignment_decode I,
        FiniteRealSupremumTasteGate_single_carrier_alignment_decode O,
        FiniteRealSupremumTasteGate_single_carrier_alignment_decode M,
        FiniteRealSupremumTasteGate_single_carrier_alignment_decode U,
        FiniteRealSupremumTasteGate_single_carrier_alignment_decode L,
        FiniteRealSupremumTasteGate_single_carrier_alignment_decode H,
        FiniteRealSupremumTasteGate_single_carrier_alignment_decode C,
        FiniteRealSupremumTasteGate_single_carrier_alignment_decode P,
        FiniteRealSupremumTasteGate_single_carrier_alignment_decode N]

private theorem FiniteRealSupremumTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteRealSupremumUp} :
    finiteRealSupremumToEventFlow x = finiteRealSupremumToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteRealSupremumFromEventFlow (finiteRealSupremumToEventFlow x) =
        finiteRealSupremumFromEventFlow (finiteRealSupremumToEventFlow y) :=
    congrArg finiteRealSupremumFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteRealSupremumTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteRealSupremumTasteGate_single_carrier_alignment_round_trip y)))

instance finiteRealSupremumBHistCarrier : BHistCarrier FiniteRealSupremumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteRealSupremumToEventFlow
  fromEventFlow := finiteRealSupremumFromEventFlow

instance finiteRealSupremumChapterTasteGate :
    ChapterTasteGate FiniteRealSupremumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteRealSupremumFromEventFlow (finiteRealSupremumToEventFlow x) = some x
    exact FiniteRealSupremumTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteRealSupremumTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem FiniteRealSupremumTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier FiniteRealSupremumUp) ∧
      Nonempty (ChapterTasteGate FiniteRealSupremumUp) ∧
        (∀ h : BHist, finiteRealSupremumDecodeBHist (finiteRealSupremumEncodeBHist h) = h) ∧
          (∀ x : FiniteRealSupremumUp,
            finiteRealSupremumFromEventFlow (finiteRealSupremumToEventFlow x) = some x) ∧
            finiteRealSupremumEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨finiteRealSupremumBHistCarrier⟩,
      ⟨finiteRealSupremumChapterTasteGate⟩,
      FiniteRealSupremumTasteGate_single_carrier_alignment_decode,
      FiniteRealSupremumTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.FiniteRealSupremumUp
