import BEDC.Derived.ResidueUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ResidueUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ResidueUp : Type where
  | mk (f center radius pole gap integral residue : BHist) : ResidueUp
  deriving DecidableEq

def residueEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: residueEncodeBHist h
  | BHist.e1 h => BMark.b1 :: residueEncodeBHist h

def residueDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (residueDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (residueDecodeBHist tail)

private theorem ResidueTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, residueDecodeBHist (residueEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def residueToEventFlow : ResidueUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ResidueUp.mk f center radius pole gap integral residue =>
      [residueEncodeBHist f,
        residueEncodeBHist center,
        residueEncodeBHist radius,
        residueEncodeBHist pole,
        residueEncodeBHist gap,
        residueEncodeBHist integral,
        residueEncodeBHist residue]

private def residueRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => residueRawAt n rest

private def residueLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => residueLengthEq n rest

def residueFromEventFlow : EventFlow → Option ResidueUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match residueLengthEq 7 flow with
      | true =>
          some
            (ResidueUp.mk
              (residueDecodeBHist (residueRawAt 0 flow))
              (residueDecodeBHist (residueRawAt 1 flow))
              (residueDecodeBHist (residueRawAt 2 flow))
              (residueDecodeBHist (residueRawAt 3 flow))
              (residueDecodeBHist (residueRawAt 4 flow))
              (residueDecodeBHist (residueRawAt 5 flow))
              (residueDecodeBHist (residueRawAt 6 flow)))
      | false => none

private theorem residue_round_trip :
    ∀ x : ResidueUp, residueFromEventFlow (residueToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk f center radius pole gap integral residue =>
      change
        some
          (ResidueUp.mk
            (residueDecodeBHist (residueEncodeBHist f))
            (residueDecodeBHist (residueEncodeBHist center))
            (residueDecodeBHist (residueEncodeBHist radius))
            (residueDecodeBHist (residueEncodeBHist pole))
            (residueDecodeBHist (residueEncodeBHist gap))
            (residueDecodeBHist (residueEncodeBHist integral))
            (residueDecodeBHist (residueEncodeBHist residue))) =
          some (ResidueUp.mk f center radius pole gap integral residue)
      rw [ResidueTasteGate_single_carrier_alignment_decode f,
        ResidueTasteGate_single_carrier_alignment_decode center,
        ResidueTasteGate_single_carrier_alignment_decode radius,
        ResidueTasteGate_single_carrier_alignment_decode pole,
        ResidueTasteGate_single_carrier_alignment_decode gap,
        ResidueTasteGate_single_carrier_alignment_decode integral,
        ResidueTasteGate_single_carrier_alignment_decode residue]

private theorem residueToEventFlow_injective {x y : ResidueUp} :
    residueToEventFlow x = residueToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      residueFromEventFlow (residueToEventFlow x) =
        residueFromEventFlow (residueToEventFlow y) :=
    congrArg residueFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (residue_round_trip x).symm
      (Eq.trans hread (residue_round_trip y)))

instance residueBHistCarrier : BHistCarrier ResidueUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := residueToEventFlow
  fromEventFlow := residueFromEventFlow

instance residueChapterTasteGate : ChapterTasteGate ResidueUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change residueFromEventFlow (residueToEventFlow x) = some x
    exact residue_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (residueToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ResidueUp :=
  -- BEDC touchpoint anchor: BHist BMark
  residueChapterTasteGate

theorem ResidueTasteGate_single_carrier_alignment :
    (forall h : BHist, residueDecodeBHist (residueEncodeBHist h) = h) ∧
      (forall x : ResidueUp, residueFromEventFlow (residueToEventFlow x) = some x) ∧
        (forall x y : ResidueUp, residueToEventFlow x = residueToEventFlow y -> x = y) ∧
          residueEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ResidueTasteGate_single_carrier_alignment_decode,
      residue_round_trip,
      fun _ _ heq => residueToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.ResidueUp
