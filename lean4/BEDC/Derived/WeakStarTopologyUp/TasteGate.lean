import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WeakStarTopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WeakStarTopologyUp : Type where
  | mk (V W L T R H C P N : BHist) : WeakStarTopologyUp
  deriving DecidableEq

def weakStarTopologyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: weakStarTopologyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: weakStarTopologyEncodeBHist h

def weakStarTopologyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (weakStarTopologyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (weakStarTopologyDecodeBHist tail)

private theorem WeakStarTopologyTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, weakStarTopologyDecodeBHist (weakStarTopologyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def weakStarTopologyFields : WeakStarTopologyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | WeakStarTopologyUp.mk V W L T R H C P N => [V, W, L, T, R, H, C, P, N]

def weakStarTopologyToEventFlow : WeakStarTopologyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map weakStarTopologyEncodeBHist (weakStarTopologyFields x)

private def weakStarTopologyEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => weakStarTopologyEventAtDefault index rest

def weakStarTopologyFromEventFlow (ef : EventFlow) : Option WeakStarTopologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (WeakStarTopologyUp.mk
      (weakStarTopologyDecodeBHist (weakStarTopologyEventAtDefault 0 ef))
      (weakStarTopologyDecodeBHist (weakStarTopologyEventAtDefault 1 ef))
      (weakStarTopologyDecodeBHist (weakStarTopologyEventAtDefault 2 ef))
      (weakStarTopologyDecodeBHist (weakStarTopologyEventAtDefault 3 ef))
      (weakStarTopologyDecodeBHist (weakStarTopologyEventAtDefault 4 ef))
      (weakStarTopologyDecodeBHist (weakStarTopologyEventAtDefault 5 ef))
      (weakStarTopologyDecodeBHist (weakStarTopologyEventAtDefault 6 ef))
      (weakStarTopologyDecodeBHist (weakStarTopologyEventAtDefault 7 ef))
      (weakStarTopologyDecodeBHist (weakStarTopologyEventAtDefault 8 ef)))

private theorem WeakStarTopologyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : WeakStarTopologyUp,
      weakStarTopologyFromEventFlow (weakStarTopologyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk V W L T R H C P N =>
      change
        some
          (WeakStarTopologyUp.mk
            (weakStarTopologyDecodeBHist (weakStarTopologyEncodeBHist V))
            (weakStarTopologyDecodeBHist (weakStarTopologyEncodeBHist W))
            (weakStarTopologyDecodeBHist (weakStarTopologyEncodeBHist L))
            (weakStarTopologyDecodeBHist (weakStarTopologyEncodeBHist T))
            (weakStarTopologyDecodeBHist (weakStarTopologyEncodeBHist R))
            (weakStarTopologyDecodeBHist (weakStarTopologyEncodeBHist H))
            (weakStarTopologyDecodeBHist (weakStarTopologyEncodeBHist C))
            (weakStarTopologyDecodeBHist (weakStarTopologyEncodeBHist P))
            (weakStarTopologyDecodeBHist (weakStarTopologyEncodeBHist N))) =
          some (WeakStarTopologyUp.mk V W L T R H C P N)
      rw [WeakStarTopologyTasteGate_single_carrier_alignment_decode_encode V,
        WeakStarTopologyTasteGate_single_carrier_alignment_decode_encode W,
        WeakStarTopologyTasteGate_single_carrier_alignment_decode_encode L,
        WeakStarTopologyTasteGate_single_carrier_alignment_decode_encode T,
        WeakStarTopologyTasteGate_single_carrier_alignment_decode_encode R,
        WeakStarTopologyTasteGate_single_carrier_alignment_decode_encode H,
        WeakStarTopologyTasteGate_single_carrier_alignment_decode_encode C,
        WeakStarTopologyTasteGate_single_carrier_alignment_decode_encode P,
        WeakStarTopologyTasteGate_single_carrier_alignment_decode_encode N]

private theorem WeakStarTopologyTasteGate_single_carrier_alignment_injective
    {x y : WeakStarTopologyUp} :
    weakStarTopologyToEventFlow x = weakStarTopologyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      weakStarTopologyFromEventFlow (weakStarTopologyToEventFlow x) =
        weakStarTopologyFromEventFlow (weakStarTopologyToEventFlow y) :=
    congrArg weakStarTopologyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (WeakStarTopologyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (WeakStarTopologyTasteGate_single_carrier_alignment_round_trip y)))

instance weakStarTopologyBHistCarrier : BHistCarrier WeakStarTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := weakStarTopologyToEventFlow
  fromEventFlow := weakStarTopologyFromEventFlow

instance weakStarTopologyChapterTasteGate : ChapterTasteGate WeakStarTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change weakStarTopologyFromEventFlow (weakStarTopologyToEventFlow x) = some x
    exact WeakStarTopologyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (WeakStarTopologyTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate WeakStarTopologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  weakStarTopologyChapterTasteGate

theorem WeakStarTopologyTasteGate_single_carrier_alignment :
    (∀ h : BHist, weakStarTopologyDecodeBHist (weakStarTopologyEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier WeakStarTopologyUp) ∧
        Nonempty (ChapterTasteGate WeakStarTopologyUp) ∧
          weakStarTopologyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨WeakStarTopologyTasteGate_single_carrier_alignment_decode_encode,
      ⟨weakStarTopologyBHistCarrier⟩,
      ⟨weakStarTopologyChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.WeakStarTopologyUp
