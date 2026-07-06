import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AssouadDimensionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AssouadDimensionUp : Type where
  | mk (X M D R S E B K Q H C P N : BHist) : AssouadDimensionUp
  deriving DecidableEq

def assouadDimensionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: assouadDimensionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: assouadDimensionEncodeBHist h

def assouadDimensionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (assouadDimensionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (assouadDimensionDecodeBHist tail)

private theorem AssouadDimensionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, assouadDimensionDecodeBHist (assouadDimensionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def assouadDimensionFields : AssouadDimensionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AssouadDimensionUp.mk X M D R S E B K Q H C P N =>
      [X, M, D, R, S, E, B, K, Q, H, C, P, N]

def assouadDimensionToEventFlow : AssouadDimensionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (assouadDimensionFields x).map assouadDimensionEncodeBHist

private def assouadDimensionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => assouadDimensionEventAtDefault index rest

def assouadDimensionFromEventFlow : EventFlow → Option AssouadDimensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (AssouadDimensionUp.mk
        (assouadDimensionDecodeBHist (assouadDimensionEventAtDefault 0 ef))
        (assouadDimensionDecodeBHist (assouadDimensionEventAtDefault 1 ef))
        (assouadDimensionDecodeBHist (assouadDimensionEventAtDefault 2 ef))
        (assouadDimensionDecodeBHist (assouadDimensionEventAtDefault 3 ef))
        (assouadDimensionDecodeBHist (assouadDimensionEventAtDefault 4 ef))
        (assouadDimensionDecodeBHist (assouadDimensionEventAtDefault 5 ef))
        (assouadDimensionDecodeBHist (assouadDimensionEventAtDefault 6 ef))
        (assouadDimensionDecodeBHist (assouadDimensionEventAtDefault 7 ef))
        (assouadDimensionDecodeBHist (assouadDimensionEventAtDefault 8 ef))
        (assouadDimensionDecodeBHist (assouadDimensionEventAtDefault 9 ef))
        (assouadDimensionDecodeBHist (assouadDimensionEventAtDefault 10 ef))
        (assouadDimensionDecodeBHist (assouadDimensionEventAtDefault 11 ef))
        (assouadDimensionDecodeBHist (assouadDimensionEventAtDefault 12 ef)))

private theorem AssouadDimensionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : AssouadDimensionUp,
      assouadDimensionFromEventFlow (assouadDimensionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X M D R S E B K Q H C P N =>
      change
        some
          (AssouadDimensionUp.mk
            (assouadDimensionDecodeBHist (assouadDimensionEncodeBHist X))
            (assouadDimensionDecodeBHist (assouadDimensionEncodeBHist M))
            (assouadDimensionDecodeBHist (assouadDimensionEncodeBHist D))
            (assouadDimensionDecodeBHist (assouadDimensionEncodeBHist R))
            (assouadDimensionDecodeBHist (assouadDimensionEncodeBHist S))
            (assouadDimensionDecodeBHist (assouadDimensionEncodeBHist E))
            (assouadDimensionDecodeBHist (assouadDimensionEncodeBHist B))
            (assouadDimensionDecodeBHist (assouadDimensionEncodeBHist K))
            (assouadDimensionDecodeBHist (assouadDimensionEncodeBHist Q))
            (assouadDimensionDecodeBHist (assouadDimensionEncodeBHist H))
            (assouadDimensionDecodeBHist (assouadDimensionEncodeBHist C))
            (assouadDimensionDecodeBHist (assouadDimensionEncodeBHist P))
            (assouadDimensionDecodeBHist (assouadDimensionEncodeBHist N))) =
          some (AssouadDimensionUp.mk X M D R S E B K Q H C P N)
      rw [AssouadDimensionTasteGate_single_carrier_alignment_decode X,
        AssouadDimensionTasteGate_single_carrier_alignment_decode M,
        AssouadDimensionTasteGate_single_carrier_alignment_decode D,
        AssouadDimensionTasteGate_single_carrier_alignment_decode R,
        AssouadDimensionTasteGate_single_carrier_alignment_decode S,
        AssouadDimensionTasteGate_single_carrier_alignment_decode E,
        AssouadDimensionTasteGate_single_carrier_alignment_decode B,
        AssouadDimensionTasteGate_single_carrier_alignment_decode K,
        AssouadDimensionTasteGate_single_carrier_alignment_decode Q,
        AssouadDimensionTasteGate_single_carrier_alignment_decode H,
        AssouadDimensionTasteGate_single_carrier_alignment_decode C,
        AssouadDimensionTasteGate_single_carrier_alignment_decode P,
        AssouadDimensionTasteGate_single_carrier_alignment_decode N]

private theorem AssouadDimensionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AssouadDimensionUp} :
    assouadDimensionToEventFlow x = assouadDimensionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      assouadDimensionFromEventFlow (assouadDimensionToEventFlow x) =
        assouadDimensionFromEventFlow (assouadDimensionToEventFlow y) :=
    congrArg assouadDimensionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AssouadDimensionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AssouadDimensionTasteGate_single_carrier_alignment_round_trip y)))

instance assouadDimensionBHistCarrier : BHistCarrier AssouadDimensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := assouadDimensionToEventFlow
  fromEventFlow := assouadDimensionFromEventFlow

instance assouadDimensionChapterTasteGate : ChapterTasteGate AssouadDimensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change assouadDimensionFromEventFlow (assouadDimensionToEventFlow x) = some x
    exact AssouadDimensionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AssouadDimensionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate AssouadDimensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  assouadDimensionChapterTasteGate

theorem AssouadDimensionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier AssouadDimensionUp) ∧
      Nonempty (ChapterTasteGate AssouadDimensionUp) ∧
        (∀ h : BHist, assouadDimensionDecodeBHist (assouadDimensionEncodeBHist h) = h) ∧
          assouadDimensionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨Nonempty.intro assouadDimensionBHistCarrier,
      Nonempty.intro assouadDimensionChapterTasteGate,
      AssouadDimensionTasteGate_single_carrier_alignment_decode,
      rfl⟩

end BEDC.Derived.AssouadDimensionUp
