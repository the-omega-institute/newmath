import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WeaklyCauchySequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WeaklyCauchySequenceUp : Type where
  | mk (S R D T E H C P N : BHist) : WeaklyCauchySequenceUp
  deriving DecidableEq

def weaklyCauchySequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: weaklyCauchySequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: weaklyCauchySequenceEncodeBHist h

def weaklyCauchySequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (weaklyCauchySequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (weaklyCauchySequenceDecodeBHist tail)

private theorem WeaklyCauchySequenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      weaklyCauchySequenceDecodeBHist (weaklyCauchySequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def weaklyCauchySequenceFields : WeaklyCauchySequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | WeaklyCauchySequenceUp.mk S R D T E H C P N => [S, R, D, T, E, H, C, P, N]

def weaklyCauchySequenceToEventFlow : WeaklyCauchySequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (weaklyCauchySequenceFields x).map weaklyCauchySequenceEncodeBHist

private def weaklyCauchySequenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => weaklyCauchySequenceEventAt index rest

def weaklyCauchySequenceFromEventFlow (ef : EventFlow) : Option WeaklyCauchySequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (WeaklyCauchySequenceUp.mk
      (weaklyCauchySequenceDecodeBHist (weaklyCauchySequenceEventAt 0 ef))
      (weaklyCauchySequenceDecodeBHist (weaklyCauchySequenceEventAt 1 ef))
      (weaklyCauchySequenceDecodeBHist (weaklyCauchySequenceEventAt 2 ef))
      (weaklyCauchySequenceDecodeBHist (weaklyCauchySequenceEventAt 3 ef))
      (weaklyCauchySequenceDecodeBHist (weaklyCauchySequenceEventAt 4 ef))
      (weaklyCauchySequenceDecodeBHist (weaklyCauchySequenceEventAt 5 ef))
      (weaklyCauchySequenceDecodeBHist (weaklyCauchySequenceEventAt 6 ef))
      (weaklyCauchySequenceDecodeBHist (weaklyCauchySequenceEventAt 7 ef))
      (weaklyCauchySequenceDecodeBHist (weaklyCauchySequenceEventAt 8 ef)))

private theorem WeaklyCauchySequenceTasteGate_single_carrier_alignment_round_trip
    (x : WeaklyCauchySequenceUp) :
    weaklyCauchySequenceFromEventFlow (weaklyCauchySequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S R D T E H C P N =>
      change
        some
          (WeaklyCauchySequenceUp.mk
            (weaklyCauchySequenceDecodeBHist (weaklyCauchySequenceEncodeBHist S))
            (weaklyCauchySequenceDecodeBHist (weaklyCauchySequenceEncodeBHist R))
            (weaklyCauchySequenceDecodeBHist (weaklyCauchySequenceEncodeBHist D))
            (weaklyCauchySequenceDecodeBHist (weaklyCauchySequenceEncodeBHist T))
            (weaklyCauchySequenceDecodeBHist (weaklyCauchySequenceEncodeBHist E))
            (weaklyCauchySequenceDecodeBHist (weaklyCauchySequenceEncodeBHist H))
            (weaklyCauchySequenceDecodeBHist (weaklyCauchySequenceEncodeBHist C))
            (weaklyCauchySequenceDecodeBHist (weaklyCauchySequenceEncodeBHist P))
            (weaklyCauchySequenceDecodeBHist (weaklyCauchySequenceEncodeBHist N))) =
          some (WeaklyCauchySequenceUp.mk S R D T E H C P N)
      rw [WeaklyCauchySequenceTasteGate_single_carrier_alignment_decode S,
        WeaklyCauchySequenceTasteGate_single_carrier_alignment_decode R,
        WeaklyCauchySequenceTasteGate_single_carrier_alignment_decode D,
        WeaklyCauchySequenceTasteGate_single_carrier_alignment_decode T,
        WeaklyCauchySequenceTasteGate_single_carrier_alignment_decode E,
        WeaklyCauchySequenceTasteGate_single_carrier_alignment_decode H,
        WeaklyCauchySequenceTasteGate_single_carrier_alignment_decode C,
        WeaklyCauchySequenceTasteGate_single_carrier_alignment_decode P,
        WeaklyCauchySequenceTasteGate_single_carrier_alignment_decode N]

private theorem WeaklyCauchySequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : WeaklyCauchySequenceUp} :
    weaklyCauchySequenceToEventFlow x = weaklyCauchySequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      weaklyCauchySequenceFromEventFlow (weaklyCauchySequenceToEventFlow x) =
        weaklyCauchySequenceFromEventFlow (weaklyCauchySequenceToEventFlow y) :=
    congrArg weaklyCauchySequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (WeaklyCauchySequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (WeaklyCauchySequenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem WeaklyCauchySequenceTasteGate_single_carrier_alignment_fields :
    ∀ x y : WeaklyCauchySequenceUp,
      weaklyCauchySequenceFields x = weaklyCauchySequenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ R₁ D₁ T₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ R₂ D₂ T₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance weaklyCauchySequenceBHistCarrier : BHistCarrier WeaklyCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := weaklyCauchySequenceToEventFlow
  fromEventFlow := weaklyCauchySequenceFromEventFlow

instance weaklyCauchySequenceChapterTasteGate :
    ChapterTasteGate WeaklyCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change weaklyCauchySequenceFromEventFlow (weaklyCauchySequenceToEventFlow x) = some x
    exact WeaklyCauchySequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (WeaklyCauchySequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem WeaklyCauchySequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, weaklyCauchySequenceDecodeBHist (weaklyCauchySequenceEncodeBHist h) = h) ∧
      (∀ x : WeaklyCauchySequenceUp,
        weaklyCauchySequenceFromEventFlow (weaklyCauchySequenceToEventFlow x) = some x) ∧
        (∀ x y : WeaklyCauchySequenceUp,
          weaklyCauchySequenceToEventFlow x = weaklyCauchySequenceToEventFlow y → x = y) ∧
          weaklyCauchySequenceEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : WeaklyCauchySequenceUp,
              weaklyCauchySequenceFields x = weaklyCauchySequenceFields y → x = y) ∧
              (∃ x y : WeaklyCauchySequenceUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨WeaklyCauchySequenceTasteGate_single_carrier_alignment_decode,
      WeaklyCauchySequenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        WeaklyCauchySequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl,
      WeaklyCauchySequenceTasteGate_single_carrier_alignment_fields,
      ⟨WeaklyCauchySequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        WeaklyCauchySequenceUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩⟩

end BEDC.Derived.WeaklyCauchySequenceUp
