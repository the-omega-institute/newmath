import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FrechetCauchyCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FrechetCauchyCriterionUp : Type where
  | mk (R S Q D K L H C P N : BHist) : FrechetCauchyCriterionUp
  deriving DecidableEq

def frechetCauchyCriterionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: frechetCauchyCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: frechetCauchyCriterionEncodeBHist h

def frechetCauchyCriterionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (frechetCauchyCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (frechetCauchyCriterionDecodeBHist tail)

private theorem FrechetCauchyCriterionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, frechetCauchyCriterionDecodeBHist (frechetCauchyCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def frechetCauchyCriterionFields : FrechetCauchyCriterionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FrechetCauchyCriterionUp.mk R S Q D K L H C P N => [R, S, Q, D, K, L, H, C, P, N]

def frechetCauchyCriterionToEventFlow : FrechetCauchyCriterionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (frechetCauchyCriterionFields x).map frechetCauchyCriterionEncodeBHist

private def frechetCauchyCriterionEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => frechetCauchyCriterionEventAtDefault index rest

def frechetCauchyCriterionFromEventFlow : EventFlow -> Option FrechetCauchyCriterionUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (FrechetCauchyCriterionUp.mk
          (frechetCauchyCriterionDecodeBHist (frechetCauchyCriterionEventAtDefault 0 ef))
          (frechetCauchyCriterionDecodeBHist (frechetCauchyCriterionEventAtDefault 1 ef))
          (frechetCauchyCriterionDecodeBHist (frechetCauchyCriterionEventAtDefault 2 ef))
          (frechetCauchyCriterionDecodeBHist (frechetCauchyCriterionEventAtDefault 3 ef))
          (frechetCauchyCriterionDecodeBHist (frechetCauchyCriterionEventAtDefault 4 ef))
          (frechetCauchyCriterionDecodeBHist (frechetCauchyCriterionEventAtDefault 5 ef))
          (frechetCauchyCriterionDecodeBHist (frechetCauchyCriterionEventAtDefault 6 ef))
          (frechetCauchyCriterionDecodeBHist (frechetCauchyCriterionEventAtDefault 7 ef))
          (frechetCauchyCriterionDecodeBHist (frechetCauchyCriterionEventAtDefault 8 ef))
          (frechetCauchyCriterionDecodeBHist (frechetCauchyCriterionEventAtDefault 9 ef)))

private theorem FrechetCauchyCriterionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FrechetCauchyCriterionUp,
      frechetCauchyCriterionFromEventFlow (frechetCauchyCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R S Q D K L H C P N =>
      change
        some
          (FrechetCauchyCriterionUp.mk
            (frechetCauchyCriterionDecodeBHist (frechetCauchyCriterionEncodeBHist R))
            (frechetCauchyCriterionDecodeBHist (frechetCauchyCriterionEncodeBHist S))
            (frechetCauchyCriterionDecodeBHist (frechetCauchyCriterionEncodeBHist Q))
            (frechetCauchyCriterionDecodeBHist (frechetCauchyCriterionEncodeBHist D))
            (frechetCauchyCriterionDecodeBHist (frechetCauchyCriterionEncodeBHist K))
            (frechetCauchyCriterionDecodeBHist (frechetCauchyCriterionEncodeBHist L))
            (frechetCauchyCriterionDecodeBHist (frechetCauchyCriterionEncodeBHist H))
            (frechetCauchyCriterionDecodeBHist (frechetCauchyCriterionEncodeBHist C))
            (frechetCauchyCriterionDecodeBHist (frechetCauchyCriterionEncodeBHist P))
            (frechetCauchyCriterionDecodeBHist (frechetCauchyCriterionEncodeBHist N))) =
          some (FrechetCauchyCriterionUp.mk R S Q D K L H C P N)
      rw [FrechetCauchyCriterionTasteGate_single_carrier_alignment_decode R,
        FrechetCauchyCriterionTasteGate_single_carrier_alignment_decode S,
        FrechetCauchyCriterionTasteGate_single_carrier_alignment_decode Q,
        FrechetCauchyCriterionTasteGate_single_carrier_alignment_decode D,
        FrechetCauchyCriterionTasteGate_single_carrier_alignment_decode K,
        FrechetCauchyCriterionTasteGate_single_carrier_alignment_decode L,
        FrechetCauchyCriterionTasteGate_single_carrier_alignment_decode H,
        FrechetCauchyCriterionTasteGate_single_carrier_alignment_decode C,
        FrechetCauchyCriterionTasteGate_single_carrier_alignment_decode P,
        FrechetCauchyCriterionTasteGate_single_carrier_alignment_decode N]

private theorem FrechetCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FrechetCauchyCriterionUp} :
    frechetCauchyCriterionToEventFlow x = frechetCauchyCriterionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      frechetCauchyCriterionFromEventFlow (frechetCauchyCriterionToEventFlow x) =
        frechetCauchyCriterionFromEventFlow (frechetCauchyCriterionToEventFlow y) :=
    congrArg frechetCauchyCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FrechetCauchyCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FrechetCauchyCriterionTasteGate_single_carrier_alignment_round_trip y)))

private theorem FrechetCauchyCriterionTasteGate_single_carrier_alignment_fields :
    ∀ x y : FrechetCauchyCriterionUp,
      frechetCauchyCriterionFields x = frechetCauchyCriterionFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 S1 Q1 D1 K1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk R2 S2 Q2 D2 K2 L2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance frechetCauchyCriterionBHistCarrier : BHistCarrier FrechetCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := frechetCauchyCriterionToEventFlow
  fromEventFlow := frechetCauchyCriterionFromEventFlow

instance frechetCauchyCriterionFieldFaithful : FieldFaithful FrechetCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := frechetCauchyCriterionFields
  field_faithful := FrechetCauchyCriterionTasteGate_single_carrier_alignment_fields

instance frechetCauchyCriterionChapterTasteGate : ChapterTasteGate FrechetCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change frechetCauchyCriterionFromEventFlow (frechetCauchyCriterionToEventFlow x) = some x
    exact FrechetCauchyCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FrechetCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance frechetCauchyCriterionNontrivial : Nontrivial FrechetCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FrechetCauchyCriterionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FrechetCauchyCriterionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FrechetCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  frechetCauchyCriterionChapterTasteGate

theorem FrechetCauchyCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist, frechetCauchyCriterionDecodeBHist (frechetCauchyCriterionEncodeBHist h) = h) ∧
      (∀ x : FrechetCauchyCriterionUp,
        frechetCauchyCriterionFromEventFlow (frechetCauchyCriterionToEventFlow x) = some x) ∧
        (∀ x y : FrechetCauchyCriterionUp,
          frechetCauchyCriterionToEventFlow x = frechetCauchyCriterionToEventFlow y -> x = y) ∧
          Nonempty (BHistCarrier FrechetCauchyCriterionUp) ∧
            Nonempty (FieldFaithful FrechetCauchyCriterionUp) ∧
              Nonempty (ChapterTasteGate FrechetCauchyCriterionUp) ∧
                frechetCauchyCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨FrechetCauchyCriterionTasteGate_single_carrier_alignment_decode,
      FrechetCauchyCriterionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        FrechetCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      ⟨frechetCauchyCriterionBHistCarrier⟩,
      ⟨frechetCauchyCriterionFieldFaithful⟩,
      ⟨frechetCauchyCriterionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.FrechetCauchyCriterionUp
