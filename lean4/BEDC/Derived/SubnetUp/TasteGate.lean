import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubnetUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SubnetUp : Type where
  | mk (I X J phi T V L H C P N : BHist) : SubnetUp
  deriving DecidableEq

def subnetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: subnetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: subnetEncodeBHist h

private def subnetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (subnetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (subnetDecodeBHist tail)

private theorem SubnetTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, subnetDecodeBHist (subnetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def subnetToEventFlow : SubnetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SubnetUp.mk I X J phi T V L H C P N =>
      [subnetEncodeBHist I,
        subnetEncodeBHist X,
        subnetEncodeBHist J,
        subnetEncodeBHist phi,
        subnetEncodeBHist T,
        subnetEncodeBHist V,
        subnetEncodeBHist L,
        subnetEncodeBHist H,
        subnetEncodeBHist C,
        subnetEncodeBHist P,
        subnetEncodeBHist N]

private def subnetEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => subnetEventAtDefault index rest

private def subnetFromEventFlow (ef : EventFlow) : Option SubnetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SubnetUp.mk
      (subnetDecodeBHist (subnetEventAtDefault 0 ef))
      (subnetDecodeBHist (subnetEventAtDefault 1 ef))
      (subnetDecodeBHist (subnetEventAtDefault 2 ef))
      (subnetDecodeBHist (subnetEventAtDefault 3 ef))
      (subnetDecodeBHist (subnetEventAtDefault 4 ef))
      (subnetDecodeBHist (subnetEventAtDefault 5 ef))
      (subnetDecodeBHist (subnetEventAtDefault 6 ef))
      (subnetDecodeBHist (subnetEventAtDefault 7 ef))
      (subnetDecodeBHist (subnetEventAtDefault 8 ef))
      (subnetDecodeBHist (subnetEventAtDefault 9 ef))
      (subnetDecodeBHist (subnetEventAtDefault 10 ef)))

private theorem SubnetTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SubnetUp, subnetFromEventFlow (subnetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I X J phi T V L H C P N =>
      change
        some
          (SubnetUp.mk
            (subnetDecodeBHist (subnetEncodeBHist I))
            (subnetDecodeBHist (subnetEncodeBHist X))
            (subnetDecodeBHist (subnetEncodeBHist J))
            (subnetDecodeBHist (subnetEncodeBHist phi))
            (subnetDecodeBHist (subnetEncodeBHist T))
            (subnetDecodeBHist (subnetEncodeBHist V))
            (subnetDecodeBHist (subnetEncodeBHist L))
            (subnetDecodeBHist (subnetEncodeBHist H))
            (subnetDecodeBHist (subnetEncodeBHist C))
            (subnetDecodeBHist (subnetEncodeBHist P))
            (subnetDecodeBHist (subnetEncodeBHist N))) =
          some (SubnetUp.mk I X J phi T V L H C P N)
      rw [SubnetTasteGate_single_carrier_alignment_decode I,
        SubnetTasteGate_single_carrier_alignment_decode X,
        SubnetTasteGate_single_carrier_alignment_decode J,
        SubnetTasteGate_single_carrier_alignment_decode phi,
        SubnetTasteGate_single_carrier_alignment_decode T,
        SubnetTasteGate_single_carrier_alignment_decode V,
        SubnetTasteGate_single_carrier_alignment_decode L,
        SubnetTasteGate_single_carrier_alignment_decode H,
        SubnetTasteGate_single_carrier_alignment_decode C,
        SubnetTasteGate_single_carrier_alignment_decode P,
        SubnetTasteGate_single_carrier_alignment_decode N]

private theorem SubnetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SubnetUp} :
    subnetToEventFlow x = subnetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      subnetFromEventFlow (subnetToEventFlow x) =
        subnetFromEventFlow (subnetToEventFlow y) :=
    congrArg subnetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SubnetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SubnetTasteGate_single_carrier_alignment_round_trip y)))

instance subnetBHistCarrier : BHistCarrier SubnetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := subnetToEventFlow
  fromEventFlow := subnetFromEventFlow

instance subnetChapterTasteGate : ChapterTasteGate SubnetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    exact SubnetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SubnetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate SubnetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  subnetChapterTasteGate

theorem SubnetTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier SubnetUp) ∧
      Nonempty (ChapterTasteGate SubnetUp) ∧
        subnetEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨subnetBHistCarrier⟩
  · constructor
    · exact ⟨subnetChapterTasteGate⟩
    · rfl

end BEDC.Derived.SubnetUp.TasteGate
