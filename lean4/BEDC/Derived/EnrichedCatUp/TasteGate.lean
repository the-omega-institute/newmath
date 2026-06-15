import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EnrichedCatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EnrichedCatUp : Type where
  | mk (C M H I K T P R : BHist) : EnrichedCatUp
  deriving DecidableEq

def enrichedCatEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: enrichedCatEncodeBHist h
  | BHist.e1 h => BMark.b1 :: enrichedCatEncodeBHist h

def enrichedCatDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (enrichedCatDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (enrichedCatDecodeBHist tail)

private theorem EnrichedCatTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, enrichedCatDecodeBHist (enrichedCatEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def enrichedCatFields : EnrichedCatUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EnrichedCatUp.mk C M H I K T P R => [C, M, H, I, K, T, P, R]

def enrichedCatToEventFlow : EnrichedCatUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (enrichedCatFields x).map enrichedCatEncodeBHist

private def EnrichedCatTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      EnrichedCatTasteGate_single_carrier_alignment_eventAt index rest

def enrichedCatFromEventFlow (ef : EventFlow) : Option EnrichedCatUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EnrichedCatUp.mk
      (enrichedCatDecodeBHist (EnrichedCatTasteGate_single_carrier_alignment_eventAt 0 ef))
      (enrichedCatDecodeBHist (EnrichedCatTasteGate_single_carrier_alignment_eventAt 1 ef))
      (enrichedCatDecodeBHist (EnrichedCatTasteGate_single_carrier_alignment_eventAt 2 ef))
      (enrichedCatDecodeBHist (EnrichedCatTasteGate_single_carrier_alignment_eventAt 3 ef))
      (enrichedCatDecodeBHist (EnrichedCatTasteGate_single_carrier_alignment_eventAt 4 ef))
      (enrichedCatDecodeBHist (EnrichedCatTasteGate_single_carrier_alignment_eventAt 5 ef))
      (enrichedCatDecodeBHist (EnrichedCatTasteGate_single_carrier_alignment_eventAt 6 ef))
      (enrichedCatDecodeBHist (EnrichedCatTasteGate_single_carrier_alignment_eventAt 7 ef)))

private theorem EnrichedCatTasteGate_single_carrier_alignment_round_trip
    (x : EnrichedCatUp) :
    enrichedCatFromEventFlow (enrichedCatToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk C M H I K T P R =>
      change
        some
          (EnrichedCatUp.mk
            (enrichedCatDecodeBHist (enrichedCatEncodeBHist C))
            (enrichedCatDecodeBHist (enrichedCatEncodeBHist M))
            (enrichedCatDecodeBHist (enrichedCatEncodeBHist H))
            (enrichedCatDecodeBHist (enrichedCatEncodeBHist I))
            (enrichedCatDecodeBHist (enrichedCatEncodeBHist K))
            (enrichedCatDecodeBHist (enrichedCatEncodeBHist T))
            (enrichedCatDecodeBHist (enrichedCatEncodeBHist P))
            (enrichedCatDecodeBHist (enrichedCatEncodeBHist R))) =
          some (EnrichedCatUp.mk C M H I K T P R)
      rw [EnrichedCatTasteGate_single_carrier_alignment_decode_encode C,
        EnrichedCatTasteGate_single_carrier_alignment_decode_encode M,
        EnrichedCatTasteGate_single_carrier_alignment_decode_encode H,
        EnrichedCatTasteGate_single_carrier_alignment_decode_encode I,
        EnrichedCatTasteGate_single_carrier_alignment_decode_encode K,
        EnrichedCatTasteGate_single_carrier_alignment_decode_encode T,
        EnrichedCatTasteGate_single_carrier_alignment_decode_encode P,
        EnrichedCatTasteGate_single_carrier_alignment_decode_encode R]

private theorem EnrichedCatTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : EnrichedCatUp} :
    enrichedCatToEventFlow x = enrichedCatToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      enrichedCatFromEventFlow (enrichedCatToEventFlow x) =
        enrichedCatFromEventFlow (enrichedCatToEventFlow y) :=
    congrArg enrichedCatFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (EnrichedCatTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (EnrichedCatTasteGate_single_carrier_alignment_round_trip y)))

instance enrichedCatBHistCarrier : BHistCarrier EnrichedCatUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := enrichedCatToEventFlow
  fromEventFlow := enrichedCatFromEventFlow

instance enrichedCatChapterTasteGate : ChapterTasteGate EnrichedCatUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change enrichedCatFromEventFlow (enrichedCatToEventFlow x) = some x
    exact EnrichedCatTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (EnrichedCatTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem EnrichedCatTasteGate_single_carrier_alignment :
    (forall h : BHist, enrichedCatDecodeBHist (enrichedCatEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier EnrichedCatUp) ∧
        Nonempty (ChapterTasteGate EnrichedCatUp) ∧
          enrichedCatEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨EnrichedCatTasteGate_single_carrier_alignment_decode_encode,
      ⟨enrichedCatBHistCarrier⟩,
      ⟨enrichedCatChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.EnrichedCatUp
