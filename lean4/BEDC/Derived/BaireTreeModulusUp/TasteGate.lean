import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BaireTreeModulusUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BaireTreeModulusUp : Type where
  | mk (B S Q W M H C P N : BHist) : BaireTreeModulusUp
  deriving DecidableEq

def baireTreeModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: baireTreeModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: baireTreeModulusEncodeBHist h

def baireTreeModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (baireTreeModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (baireTreeModulusDecodeBHist tail)

private theorem baireTreeModulusDecodeEncodeBHist :
    ∀ h : BHist, baireTreeModulusDecodeBHist (baireTreeModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def baireTreeModulusFields : BaireTreeModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BaireTreeModulusUp.mk B S Q W M H C P N => [B, S, Q, W, M, H, C, P, N]

def baireTreeModulusToEventFlow : BaireTreeModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (baireTreeModulusFields x).map baireTreeModulusEncodeBHist

private def baireTreeModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => baireTreeModulusEventAtDefault index rest

def baireTreeModulusFromEventFlow
    (flow : EventFlow) : Option BaireTreeModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BaireTreeModulusUp.mk
      (baireTreeModulusDecodeBHist (baireTreeModulusEventAtDefault 0 flow))
      (baireTreeModulusDecodeBHist (baireTreeModulusEventAtDefault 1 flow))
      (baireTreeModulusDecodeBHist (baireTreeModulusEventAtDefault 2 flow))
      (baireTreeModulusDecodeBHist (baireTreeModulusEventAtDefault 3 flow))
      (baireTreeModulusDecodeBHist (baireTreeModulusEventAtDefault 4 flow))
      (baireTreeModulusDecodeBHist (baireTreeModulusEventAtDefault 5 flow))
      (baireTreeModulusDecodeBHist (baireTreeModulusEventAtDefault 6 flow))
      (baireTreeModulusDecodeBHist (baireTreeModulusEventAtDefault 7 flow))
      (baireTreeModulusDecodeBHist (baireTreeModulusEventAtDefault 8 flow)))

private theorem baireTreeModulus_round_trip :
    ∀ x : BaireTreeModulusUp,
      baireTreeModulusFromEventFlow (baireTreeModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B S Q W M H C P N =>
      change
        some
          (BaireTreeModulusUp.mk
            (baireTreeModulusDecodeBHist (baireTreeModulusEncodeBHist B))
            (baireTreeModulusDecodeBHist (baireTreeModulusEncodeBHist S))
            (baireTreeModulusDecodeBHist (baireTreeModulusEncodeBHist Q))
            (baireTreeModulusDecodeBHist (baireTreeModulusEncodeBHist W))
            (baireTreeModulusDecodeBHist (baireTreeModulusEncodeBHist M))
            (baireTreeModulusDecodeBHist (baireTreeModulusEncodeBHist H))
            (baireTreeModulusDecodeBHist (baireTreeModulusEncodeBHist C))
            (baireTreeModulusDecodeBHist (baireTreeModulusEncodeBHist P))
            (baireTreeModulusDecodeBHist (baireTreeModulusEncodeBHist N))) =
          some (BaireTreeModulusUp.mk B S Q W M H C P N)
      rw [baireTreeModulusDecodeEncodeBHist B,
        baireTreeModulusDecodeEncodeBHist S,
        baireTreeModulusDecodeEncodeBHist Q,
        baireTreeModulusDecodeEncodeBHist W,
        baireTreeModulusDecodeEncodeBHist M,
        baireTreeModulusDecodeEncodeBHist H,
        baireTreeModulusDecodeEncodeBHist C,
        baireTreeModulusDecodeEncodeBHist P,
        baireTreeModulusDecodeEncodeBHist N]

private theorem baireTreeModulusToEventFlow_injective
    {x y : BaireTreeModulusUp} :
    baireTreeModulusToEventFlow x = baireTreeModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      baireTreeModulusFromEventFlow (baireTreeModulusToEventFlow x) =
        baireTreeModulusFromEventFlow (baireTreeModulusToEventFlow y) :=
    congrArg baireTreeModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (baireTreeModulus_round_trip x).symm
      (Eq.trans hread (baireTreeModulus_round_trip y)))

private theorem baireTreeModulus_fields_faithful :
    ∀ x y : BaireTreeModulusUp,
      baireTreeModulusFields x = baireTreeModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x
  cases y
  cases hfields
  rfl

instance baireTreeModulusBHistCarrier : BHistCarrier BaireTreeModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := baireTreeModulusToEventFlow
  fromEventFlow := baireTreeModulusFromEventFlow

instance baireTreeModulusChapterTasteGate : ChapterTasteGate BaireTreeModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change baireTreeModulusFromEventFlow (baireTreeModulusToEventFlow x) = some x
    exact baireTreeModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (baireTreeModulusToEventFlow_injective heq)

instance baireTreeModulusFieldFaithful : FieldFaithful BaireTreeModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := baireTreeModulusFields
  field_faithful := baireTreeModulus_fields_faithful

instance baireTreeModulusNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BaireTreeModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BaireTreeModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BaireTreeModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BaireTreeModulusTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BaireTreeModulusUp) ∧
      Nonempty (FieldFaithful BaireTreeModulusUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial BaireTreeModulusUp) ∧
      (∀ h : BHist, baireTreeModulusDecodeBHist (baireTreeModulusEncodeBHist h) = h) ∧
      baireTreeModulusDecodeBHist (BMark.b1 :: []) = BHist.e1 BHist.Empty ∧
      (∀ x y : BaireTreeModulusUp,
        baireTreeModulusFields x = baireTreeModulusFields y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨baireTreeModulusChapterTasteGate⟩,
      ⟨baireTreeModulusFieldFaithful⟩,
      ⟨baireTreeModulusNontrivial⟩,
      baireTreeModulusDecodeEncodeBHist,
      rfl,
      baireTreeModulus_fields_faithful⟩

end BEDC.Derived.BaireTreeModulusUp.TasteGate
