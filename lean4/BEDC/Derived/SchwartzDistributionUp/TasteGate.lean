import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SchwartzDistributionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SchwartzDistributionUp : Type where
  | mk (S T A W Q E L H C P N : BHist) : SchwartzDistributionUp
  deriving DecidableEq

def schwartzDistributionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: schwartzDistributionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: schwartzDistributionEncodeBHist h

def schwartzDistributionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (schwartzDistributionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (schwartzDistributionDecodeBHist tail)

private theorem SchwartzDistributionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      schwartzDistributionDecodeBHist (schwartzDistributionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def schwartzDistributionFields : SchwartzDistributionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SchwartzDistributionUp.mk S T A W Q E L H C P N => [S, T, A, W, Q, E, L, H, C, P, N]

def schwartzDistributionToEventFlow : SchwartzDistributionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (schwartzDistributionFields x).map schwartzDistributionEncodeBHist

private def schwartzDistributionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => schwartzDistributionEventAtDefault index rest

def schwartzDistributionFromEventFlow : EventFlow → Option SchwartzDistributionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (SchwartzDistributionUp.mk
        (schwartzDistributionDecodeBHist (schwartzDistributionEventAtDefault 0 ef))
        (schwartzDistributionDecodeBHist (schwartzDistributionEventAtDefault 1 ef))
        (schwartzDistributionDecodeBHist (schwartzDistributionEventAtDefault 2 ef))
        (schwartzDistributionDecodeBHist (schwartzDistributionEventAtDefault 3 ef))
        (schwartzDistributionDecodeBHist (schwartzDistributionEventAtDefault 4 ef))
        (schwartzDistributionDecodeBHist (schwartzDistributionEventAtDefault 5 ef))
        (schwartzDistributionDecodeBHist (schwartzDistributionEventAtDefault 6 ef))
        (schwartzDistributionDecodeBHist (schwartzDistributionEventAtDefault 7 ef))
        (schwartzDistributionDecodeBHist (schwartzDistributionEventAtDefault 8 ef))
        (schwartzDistributionDecodeBHist (schwartzDistributionEventAtDefault 9 ef))
        (schwartzDistributionDecodeBHist (schwartzDistributionEventAtDefault 10 ef)))

private theorem SchwartzDistributionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SchwartzDistributionUp,
      schwartzDistributionFromEventFlow (schwartzDistributionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T A W Q E L H C P N =>
      change
        some
          (SchwartzDistributionUp.mk
            (schwartzDistributionDecodeBHist (schwartzDistributionEncodeBHist S))
            (schwartzDistributionDecodeBHist (schwartzDistributionEncodeBHist T))
            (schwartzDistributionDecodeBHist (schwartzDistributionEncodeBHist A))
            (schwartzDistributionDecodeBHist (schwartzDistributionEncodeBHist W))
            (schwartzDistributionDecodeBHist (schwartzDistributionEncodeBHist Q))
            (schwartzDistributionDecodeBHist (schwartzDistributionEncodeBHist E))
            (schwartzDistributionDecodeBHist (schwartzDistributionEncodeBHist L))
            (schwartzDistributionDecodeBHist (schwartzDistributionEncodeBHist H))
            (schwartzDistributionDecodeBHist (schwartzDistributionEncodeBHist C))
            (schwartzDistributionDecodeBHist (schwartzDistributionEncodeBHist P))
            (schwartzDistributionDecodeBHist (schwartzDistributionEncodeBHist N))) =
          some (SchwartzDistributionUp.mk S T A W Q E L H C P N)
      rw [SchwartzDistributionTasteGate_single_carrier_alignment_decode S,
        SchwartzDistributionTasteGate_single_carrier_alignment_decode T,
        SchwartzDistributionTasteGate_single_carrier_alignment_decode A,
        SchwartzDistributionTasteGate_single_carrier_alignment_decode W,
        SchwartzDistributionTasteGate_single_carrier_alignment_decode Q,
        SchwartzDistributionTasteGate_single_carrier_alignment_decode E,
        SchwartzDistributionTasteGate_single_carrier_alignment_decode L,
        SchwartzDistributionTasteGate_single_carrier_alignment_decode H,
        SchwartzDistributionTasteGate_single_carrier_alignment_decode C,
        SchwartzDistributionTasteGate_single_carrier_alignment_decode P,
        SchwartzDistributionTasteGate_single_carrier_alignment_decode N]

private theorem SchwartzDistributionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SchwartzDistributionUp} :
    schwartzDistributionToEventFlow x = schwartzDistributionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      schwartzDistributionFromEventFlow (schwartzDistributionToEventFlow x) =
        schwartzDistributionFromEventFlow (schwartzDistributionToEventFlow y) :=
    congrArg schwartzDistributionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SchwartzDistributionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SchwartzDistributionTasteGate_single_carrier_alignment_round_trip y)))

instance schwartzDistributionBHistCarrier : BHistCarrier SchwartzDistributionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := schwartzDistributionToEventFlow
  fromEventFlow := schwartzDistributionFromEventFlow

instance schwartzDistributionChapterTasteGate : ChapterTasteGate SchwartzDistributionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change schwartzDistributionFromEventFlow (schwartzDistributionToEventFlow x) = some x
    exact SchwartzDistributionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SchwartzDistributionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate SchwartzDistributionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  schwartzDistributionChapterTasteGate

theorem SchwartzDistributionTasteGate_single_carrier_alignment :
    (∀ h : BHist, schwartzDistributionDecodeBHist (schwartzDistributionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SchwartzDistributionUp) ∧
        Nonempty (ChapterTasteGate SchwartzDistributionUp) ∧
          schwartzDistributionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨SchwartzDistributionTasteGate_single_carrier_alignment_decode,
      ⟨schwartzDistributionBHistCarrier⟩,
      ⟨schwartzDistributionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.SchwartzDistributionUp
