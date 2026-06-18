import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RuleOneTenCausalConeUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RuleOneTenCausalConeUp : Type where
  | mk (I U T L B O H C P N : BHist) : RuleOneTenCausalConeUp
  deriving DecidableEq

def ruleOneTenCausalConeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ruleOneTenCausalConeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: ruleOneTenCausalConeEncodeBHist h

def ruleOneTenCausalConeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (ruleOneTenCausalConeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (ruleOneTenCausalConeDecodeBHist tail)

private theorem ruleOneTenCausalConeDecodeEncodeBHist :
    ∀ h : BHist, ruleOneTenCausalConeDecodeBHist
      (ruleOneTenCausalConeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ruleOneTenCausalConeFields : RuleOneTenCausalConeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RuleOneTenCausalConeUp.mk I U T L B O H C P N => [I, U, T, L, B, O, H, C, P, N]

def ruleOneTenCausalConeToEventFlow : RuleOneTenCausalConeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (ruleOneTenCausalConeFields x).map ruleOneTenCausalConeEncodeBHist

private def ruleOneTenCausalConeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => ruleOneTenCausalConeEventAtDefault index rest

def ruleOneTenCausalConeFromEventFlow
    (flow : EventFlow) : Option RuleOneTenCausalConeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RuleOneTenCausalConeUp.mk
      (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEventAtDefault 0 flow))
      (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEventAtDefault 1 flow))
      (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEventAtDefault 2 flow))
      (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEventAtDefault 3 flow))
      (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEventAtDefault 4 flow))
      (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEventAtDefault 5 flow))
      (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEventAtDefault 6 flow))
      (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEventAtDefault 7 flow))
      (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEventAtDefault 8 flow))
      (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEventAtDefault 9 flow)))

private theorem ruleOneTenCausalCone_round_trip :
    ∀ x : RuleOneTenCausalConeUp,
      ruleOneTenCausalConeFromEventFlow (ruleOneTenCausalConeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I U T L B O H C P N =>
      change
        some
          (RuleOneTenCausalConeUp.mk
            (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEncodeBHist I))
            (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEncodeBHist U))
            (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEncodeBHist T))
            (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEncodeBHist L))
            (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEncodeBHist B))
            (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEncodeBHist O))
            (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEncodeBHist H))
            (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEncodeBHist C))
            (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEncodeBHist P))
            (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEncodeBHist N))) =
          some (RuleOneTenCausalConeUp.mk I U T L B O H C P N)
      rw [ruleOneTenCausalConeDecodeEncodeBHist I,
        ruleOneTenCausalConeDecodeEncodeBHist U,
        ruleOneTenCausalConeDecodeEncodeBHist T,
        ruleOneTenCausalConeDecodeEncodeBHist L,
        ruleOneTenCausalConeDecodeEncodeBHist B,
        ruleOneTenCausalConeDecodeEncodeBHist O,
        ruleOneTenCausalConeDecodeEncodeBHist H,
        ruleOneTenCausalConeDecodeEncodeBHist C,
        ruleOneTenCausalConeDecodeEncodeBHist P,
        ruleOneTenCausalConeDecodeEncodeBHist N]

private theorem ruleOneTenCausalConeToEventFlow_injective
    {x y : RuleOneTenCausalConeUp} :
    ruleOneTenCausalConeToEventFlow x = ruleOneTenCausalConeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ruleOneTenCausalConeFromEventFlow (ruleOneTenCausalConeToEventFlow x) =
        ruleOneTenCausalConeFromEventFlow (ruleOneTenCausalConeToEventFlow y) :=
    congrArg ruleOneTenCausalConeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ruleOneTenCausalCone_round_trip x).symm
      (Eq.trans hread (ruleOneTenCausalCone_round_trip y)))

private theorem ruleOneTenCausalCone_fields_faithful :
    ∀ x y : RuleOneTenCausalConeUp,
      ruleOneTenCausalConeFields x = ruleOneTenCausalConeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x
  cases y
  cases hfields
  rfl

instance ruleOneTenCausalConeBHistCarrier : BHistCarrier RuleOneTenCausalConeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ruleOneTenCausalConeToEventFlow
  fromEventFlow := ruleOneTenCausalConeFromEventFlow

instance ruleOneTenCausalConeChapterTasteGate : ChapterTasteGate RuleOneTenCausalConeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change ruleOneTenCausalConeFromEventFlow (ruleOneTenCausalConeToEventFlow x) = some x
    exact ruleOneTenCausalCone_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ruleOneTenCausalConeToEventFlow_injective heq)

instance ruleOneTenCausalConeFieldFaithful : FieldFaithful RuleOneTenCausalConeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := ruleOneTenCausalConeFields
  field_faithful := ruleOneTenCausalCone_fields_faithful

instance ruleOneTenCausalConeNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RuleOneTenCausalConeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RuleOneTenCausalConeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RuleOneTenCausalConeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RuleOneTenCausalConeTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RuleOneTenCausalConeUp) ∧
      Nonempty (FieldFaithful RuleOneTenCausalConeUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial RuleOneTenCausalConeUp) ∧
      (∀ h : BHist,
        ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEncodeBHist h) = h) ∧
      ruleOneTenCausalConeDecodeBHist (BMark.b0 :: []) = BHist.e0 BHist.Empty ∧
      (∀ x y : RuleOneTenCausalConeUp,
        ruleOneTenCausalConeFields x = ruleOneTenCausalConeFields y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨ruleOneTenCausalConeChapterTasteGate⟩,
      ⟨ruleOneTenCausalConeFieldFaithful⟩,
      ⟨ruleOneTenCausalConeNontrivial⟩,
      ruleOneTenCausalConeDecodeEncodeBHist,
      rfl,
      ruleOneTenCausalCone_fields_faithful⟩

end BEDC.Derived.RuleOneTenCausalConeUp.TasteGate
