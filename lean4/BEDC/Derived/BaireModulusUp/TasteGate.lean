import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BaireModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BaireModulusUp : Type where
  | mk (B S W mu R H C P N : BHist) : BaireModulusUp

def baireModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: baireModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: baireModulusEncodeBHist h

def baireModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (baireModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (baireModulusDecodeBHist tail)

private theorem baireModulusDecodeEncodeBHist :
    ∀ h : BHist, baireModulusDecodeBHist (baireModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def baireModulusFields : BaireModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BaireModulusUp.mk B S W mu R H C P N => [B, S, W, mu, R, H, C, P, N]

def baireModulusToEventFlow : BaireModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (baireModulusFields x).map baireModulusEncodeBHist

private def baireModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => baireModulusEventAtDefault index rest

def baireModulusFromEventFlow (ef : EventFlow) : Option BaireModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BaireModulusUp.mk
      (baireModulusDecodeBHist (baireModulusEventAtDefault 0 ef))
      (baireModulusDecodeBHist (baireModulusEventAtDefault 1 ef))
      (baireModulusDecodeBHist (baireModulusEventAtDefault 2 ef))
      (baireModulusDecodeBHist (baireModulusEventAtDefault 3 ef))
      (baireModulusDecodeBHist (baireModulusEventAtDefault 4 ef))
      (baireModulusDecodeBHist (baireModulusEventAtDefault 5 ef))
      (baireModulusDecodeBHist (baireModulusEventAtDefault 6 ef))
      (baireModulusDecodeBHist (baireModulusEventAtDefault 7 ef))
      (baireModulusDecodeBHist (baireModulusEventAtDefault 8 ef)))

private theorem baireModulus_round_trip :
    ∀ x : BaireModulusUp,
      baireModulusFromEventFlow (baireModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B S W mu R H C P N =>
      change
        some
            (BaireModulusUp.mk
              (baireModulusDecodeBHist (baireModulusEncodeBHist B))
              (baireModulusDecodeBHist (baireModulusEncodeBHist S))
              (baireModulusDecodeBHist (baireModulusEncodeBHist W))
              (baireModulusDecodeBHist (baireModulusEncodeBHist mu))
              (baireModulusDecodeBHist (baireModulusEncodeBHist R))
              (baireModulusDecodeBHist (baireModulusEncodeBHist H))
              (baireModulusDecodeBHist (baireModulusEncodeBHist C))
              (baireModulusDecodeBHist (baireModulusEncodeBHist P))
              (baireModulusDecodeBHist (baireModulusEncodeBHist N))) =
          some (BaireModulusUp.mk B S W mu R H C P N)
      rw [baireModulusDecodeEncodeBHist B, baireModulusDecodeEncodeBHist S,
        baireModulusDecodeEncodeBHist W, baireModulusDecodeEncodeBHist mu,
        baireModulusDecodeEncodeBHist R, baireModulusDecodeEncodeBHist H,
        baireModulusDecodeEncodeBHist C, baireModulusDecodeEncodeBHist P,
        baireModulusDecodeEncodeBHist N]

private theorem baireModulusToEventFlow_injective {x y : BaireModulusUp} :
    baireModulusToEventFlow x = baireModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      baireModulusFromEventFlow (baireModulusToEventFlow x) =
        baireModulusFromEventFlow (baireModulusToEventFlow y) :=
    congrArg baireModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (baireModulus_round_trip x).symm
      (Eq.trans hread (baireModulus_round_trip y)))

private theorem baireModulus_fields_faithful :
    ∀ x y : BaireModulusUp, baireModulusFields x = baireModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B₁ S₁ W₁ mu₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ S₂ W₂ mu₂ R₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance baireModulusBHistCarrier : BHistCarrier BaireModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := baireModulusToEventFlow
  fromEventFlow := baireModulusFromEventFlow

instance baireModulusChapterTasteGate : ChapterTasteGate BaireModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change baireModulusFromEventFlow (baireModulusToEventFlow x) = some x
    exact baireModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (baireModulusToEventFlow_injective heq)

instance baireModulusFieldFaithful : FieldFaithful BaireModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := baireModulusFields
  field_faithful := baireModulus_fields_faithful

instance baireModulusNontrivial : BEDC.Meta.TasteGate.Nontrivial BaireModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BaireModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BaireModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BaireModulusTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BaireModulusUp) ∧ Nonempty (FieldFaithful BaireModulusUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial BaireModulusUp) ∧
        (∀ h : BHist, baireModulusDecodeBHist (baireModulusEncodeBHist h) = h) ∧
          (∀ x : BaireModulusUp,
            baireModulusFromEventFlow (baireModulusToEventFlow x) = some x) ∧
            (∀ x y : BaireModulusUp,
              baireModulusToEventFlow x = baireModulusToEventFlow y → x = y) ∧
              baireModulusEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact
      ⟨{
        round_trip := by
          intro x
          change baireModulusFromEventFlow (baireModulusToEventFlow x) = some x
          exact baireModulus_round_trip x
        layer_separation := by
          intro x y hxy heq
          exact hxy (baireModulusToEventFlow_injective heq)
      }⟩
  · constructor
    · exact
        ⟨{
          fields := baireModulusFields
          field_faithful := baireModulus_fields_faithful
        }⟩
    · constructor
      · exact
          ⟨{
            witness_pair :=
              ⟨BaireModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                BaireModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩
          }⟩
      · exact
          ⟨baireModulusDecodeEncodeBHist, baireModulus_round_trip,
            (fun _ _ heq => baireModulusToEventFlow_injective heq), rfl⟩

end BEDC.Derived.BaireModulusUp
