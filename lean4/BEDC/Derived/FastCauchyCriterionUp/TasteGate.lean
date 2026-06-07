import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FastCauchyCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FastCauchyCriterionUp : Type where
  | mk (S D M R E H C P N : BHist) : FastCauchyCriterionUp
  deriving DecidableEq

def fastCauchyCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fastCauchyCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fastCauchyCriterionEncodeBHist h

def fastCauchyCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fastCauchyCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fastCauchyCriterionDecodeBHist tail)

private theorem FastCauchyCriterionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, fastCauchyCriterionDecodeBHist (fastCauchyCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fastCauchyCriterionFields : FastCauchyCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FastCauchyCriterionUp.mk S D M R E H C P N => [S, D, M, R, E, H, C, P, N]

def fastCauchyCriterionToEventFlow : FastCauchyCriterionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (fastCauchyCriterionFields x).map fastCauchyCriterionEncodeBHist

private def fastCauchyCriterionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => fastCauchyCriterionEventAtDefault index rest

def fastCauchyCriterionFromEventFlow (ef : EventFlow) : Option FastCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FastCauchyCriterionUp.mk
      (fastCauchyCriterionDecodeBHist (fastCauchyCriterionEventAtDefault 0 ef))
      (fastCauchyCriterionDecodeBHist (fastCauchyCriterionEventAtDefault 1 ef))
      (fastCauchyCriterionDecodeBHist (fastCauchyCriterionEventAtDefault 2 ef))
      (fastCauchyCriterionDecodeBHist (fastCauchyCriterionEventAtDefault 3 ef))
      (fastCauchyCriterionDecodeBHist (fastCauchyCriterionEventAtDefault 4 ef))
      (fastCauchyCriterionDecodeBHist (fastCauchyCriterionEventAtDefault 5 ef))
      (fastCauchyCriterionDecodeBHist (fastCauchyCriterionEventAtDefault 6 ef))
      (fastCauchyCriterionDecodeBHist (fastCauchyCriterionEventAtDefault 7 ef))
      (fastCauchyCriterionDecodeBHist (fastCauchyCriterionEventAtDefault 8 ef)))

private theorem fastCauchyCriterion_round_trip :
    ∀ x : FastCauchyCriterionUp,
      fastCauchyCriterionFromEventFlow (fastCauchyCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S D M R E H C P N =>
      change
        some
            (FastCauchyCriterionUp.mk
              (fastCauchyCriterionDecodeBHist (fastCauchyCriterionEncodeBHist S))
              (fastCauchyCriterionDecodeBHist (fastCauchyCriterionEncodeBHist D))
              (fastCauchyCriterionDecodeBHist (fastCauchyCriterionEncodeBHist M))
              (fastCauchyCriterionDecodeBHist (fastCauchyCriterionEncodeBHist R))
              (fastCauchyCriterionDecodeBHist (fastCauchyCriterionEncodeBHist E))
              (fastCauchyCriterionDecodeBHist (fastCauchyCriterionEncodeBHist H))
              (fastCauchyCriterionDecodeBHist (fastCauchyCriterionEncodeBHist C))
              (fastCauchyCriterionDecodeBHist (fastCauchyCriterionEncodeBHist P))
              (fastCauchyCriterionDecodeBHist (fastCauchyCriterionEncodeBHist N))) =
          some (FastCauchyCriterionUp.mk S D M R E H C P N)
      rw [FastCauchyCriterionTasteGate_single_carrier_alignment_decode S,
        FastCauchyCriterionTasteGate_single_carrier_alignment_decode D,
        FastCauchyCriterionTasteGate_single_carrier_alignment_decode M,
        FastCauchyCriterionTasteGate_single_carrier_alignment_decode R,
        FastCauchyCriterionTasteGate_single_carrier_alignment_decode E,
        FastCauchyCriterionTasteGate_single_carrier_alignment_decode H,
        FastCauchyCriterionTasteGate_single_carrier_alignment_decode C,
        FastCauchyCriterionTasteGate_single_carrier_alignment_decode P,
        FastCauchyCriterionTasteGate_single_carrier_alignment_decode N]

private theorem fastCauchyCriterionToEventFlow_injective
    {x y : FastCauchyCriterionUp} :
    fastCauchyCriterionToEventFlow x = fastCauchyCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fastCauchyCriterionFromEventFlow (fastCauchyCriterionToEventFlow x) =
        fastCauchyCriterionFromEventFlow (fastCauchyCriterionToEventFlow y) :=
    congrArg fastCauchyCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fastCauchyCriterion_round_trip x).symm
      (Eq.trans hread (fastCauchyCriterion_round_trip y)))

instance fastCauchyCriterionBHistCarrier : BHistCarrier FastCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fastCauchyCriterionToEventFlow
  fromEventFlow := fastCauchyCriterionFromEventFlow

instance fastCauchyCriterionChapterTasteGate :
    ChapterTasteGate FastCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fastCauchyCriterionFromEventFlow (fastCauchyCriterionToEventFlow x) = some x
    exact fastCauchyCriterion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fastCauchyCriterionToEventFlow_injective heq)

theorem FastCauchyCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist, fastCauchyCriterionDecodeBHist (fastCauchyCriterionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier FastCauchyCriterionUp) ∧
        Nonempty (ChapterTasteGate FastCauchyCriterionUp) ∧
          fastCauchyCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FastCauchyCriterionTasteGate_single_carrier_alignment_decode,
      ⟨fastCauchyCriterionBHistCarrier⟩,
      ⟨fastCauchyCriterionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.FastCauchyCriterionUp
