import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WeakTopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WeakTopologyUp : Type where
  | mk (V F U T R H C P N : BHist) : WeakTopologyUp
  deriving DecidableEq

def weakTopologyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: weakTopologyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: weakTopologyEncodeBHist h

def weakTopologyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (weakTopologyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (weakTopologyDecodeBHist tail)

private theorem WeakTopologyTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, weakTopologyDecodeBHist (weakTopologyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def weakTopologyFields : WeakTopologyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | WeakTopologyUp.mk V F U T R H C P N => [V, F, U, T, R, H, C, P, N]

def weakTopologyToEventFlow : WeakTopologyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (weakTopologyFields x).map weakTopologyEncodeBHist

private def WeakTopologyTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      WeakTopologyTasteGate_single_carrier_alignment_eventAt index rest

def weakTopologyFromEventFlow (ef : EventFlow) : Option WeakTopologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (WeakTopologyUp.mk
      (weakTopologyDecodeBHist (WeakTopologyTasteGate_single_carrier_alignment_eventAt 0 ef))
      (weakTopologyDecodeBHist (WeakTopologyTasteGate_single_carrier_alignment_eventAt 1 ef))
      (weakTopologyDecodeBHist (WeakTopologyTasteGate_single_carrier_alignment_eventAt 2 ef))
      (weakTopologyDecodeBHist (WeakTopologyTasteGate_single_carrier_alignment_eventAt 3 ef))
      (weakTopologyDecodeBHist (WeakTopologyTasteGate_single_carrier_alignment_eventAt 4 ef))
      (weakTopologyDecodeBHist (WeakTopologyTasteGate_single_carrier_alignment_eventAt 5 ef))
      (weakTopologyDecodeBHist (WeakTopologyTasteGate_single_carrier_alignment_eventAt 6 ef))
      (weakTopologyDecodeBHist (WeakTopologyTasteGate_single_carrier_alignment_eventAt 7 ef))
      (weakTopologyDecodeBHist (WeakTopologyTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem WeakTopologyTasteGate_single_carrier_alignment_round_trip
    (x : WeakTopologyUp) :
    weakTopologyFromEventFlow (weakTopologyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk V F U T R H C P N =>
      change
        some
          (WeakTopologyUp.mk
            (weakTopologyDecodeBHist (weakTopologyEncodeBHist V))
            (weakTopologyDecodeBHist (weakTopologyEncodeBHist F))
            (weakTopologyDecodeBHist (weakTopologyEncodeBHist U))
            (weakTopologyDecodeBHist (weakTopologyEncodeBHist T))
            (weakTopologyDecodeBHist (weakTopologyEncodeBHist R))
            (weakTopologyDecodeBHist (weakTopologyEncodeBHist H))
            (weakTopologyDecodeBHist (weakTopologyEncodeBHist C))
            (weakTopologyDecodeBHist (weakTopologyEncodeBHist P))
            (weakTopologyDecodeBHist (weakTopologyEncodeBHist N))) =
          some (WeakTopologyUp.mk V F U T R H C P N)
      rw [WeakTopologyTasteGate_single_carrier_alignment_decode V,
        WeakTopologyTasteGate_single_carrier_alignment_decode F,
        WeakTopologyTasteGate_single_carrier_alignment_decode U,
        WeakTopologyTasteGate_single_carrier_alignment_decode T,
        WeakTopologyTasteGate_single_carrier_alignment_decode R,
        WeakTopologyTasteGate_single_carrier_alignment_decode H,
        WeakTopologyTasteGate_single_carrier_alignment_decode C,
        WeakTopologyTasteGate_single_carrier_alignment_decode P,
        WeakTopologyTasteGate_single_carrier_alignment_decode N]

private theorem WeakTopologyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : WeakTopologyUp} :
    weakTopologyToEventFlow x = weakTopologyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      weakTopologyFromEventFlow (weakTopologyToEventFlow x) =
        weakTopologyFromEventFlow (weakTopologyToEventFlow y) :=
    congrArg weakTopologyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (WeakTopologyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (WeakTopologyTasteGate_single_carrier_alignment_round_trip y)))

instance weakTopologyBHistCarrier : BHistCarrier WeakTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := weakTopologyToEventFlow
  fromEventFlow := weakTopologyFromEventFlow

instance weakTopologyChapterTasteGate : ChapterTasteGate WeakTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change weakTopologyFromEventFlow (weakTopologyToEventFlow x) = some x
    exact WeakTopologyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (WeakTopologyTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate WeakTopologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  weakTopologyChapterTasteGate

theorem WeakTopologyTasteGate_single_carrier_alignment :
    (forall h : BHist, weakTopologyDecodeBHist (weakTopologyEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier WeakTopologyUp) ∧
        Nonempty (ChapterTasteGate WeakTopologyUp) ∧
          weakTopologyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨WeakTopologyTasteGate_single_carrier_alignment_decode,
      ⟨weakTopologyBHistCarrier⟩,
      ⟨weakTopologyChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.WeakTopologyUp
