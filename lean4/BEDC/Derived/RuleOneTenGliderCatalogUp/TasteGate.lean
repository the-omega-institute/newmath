import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RuleOneTenGliderCatalogUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RuleOneTenGliderCatalogUp : Type where
  | mk (R W G P D H C K N : BHist) : RuleOneTenGliderCatalogUp
  deriving DecidableEq

def ruleOneTenGliderCatalogEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ruleOneTenGliderCatalogEncodeBHist h
  | BHist.e1 h => BMark.b1 :: ruleOneTenGliderCatalogEncodeBHist h

def ruleOneTenGliderCatalogDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (ruleOneTenGliderCatalogDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (ruleOneTenGliderCatalogDecodeBHist tail)

private theorem RuleOneTenGliderCatalogTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      ruleOneTenGliderCatalogDecodeBHist (ruleOneTenGliderCatalogEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ruleOneTenGliderCatalogFields : RuleOneTenGliderCatalogUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RuleOneTenGliderCatalogUp.mk R W G P D H C K N => [R, W, G, P, D, H, C, K, N]

def ruleOneTenGliderCatalogToEventFlow : RuleOneTenGliderCatalogUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RuleOneTenGliderCatalogUp.mk R W G P D H C K N =>
      [[BMark.b0],
        ruleOneTenGliderCatalogEncodeBHist R,
        [BMark.b1, BMark.b0],
        ruleOneTenGliderCatalogEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b0],
        ruleOneTenGliderCatalogEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        ruleOneTenGliderCatalogEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        ruleOneTenGliderCatalogEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        ruleOneTenGliderCatalogEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        ruleOneTenGliderCatalogEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        ruleOneTenGliderCatalogEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        ruleOneTenGliderCatalogEncodeBHist N]

private def ruleOneTenGliderCatalogEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => ruleOneTenGliderCatalogEventAtDefault index rest

def ruleOneTenGliderCatalogFromEventFlow
    (ef : EventFlow) : Option RuleOneTenGliderCatalogUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RuleOneTenGliderCatalogUp.mk
      (ruleOneTenGliderCatalogDecodeBHist (ruleOneTenGliderCatalogEventAtDefault 1 ef))
      (ruleOneTenGliderCatalogDecodeBHist (ruleOneTenGliderCatalogEventAtDefault 3 ef))
      (ruleOneTenGliderCatalogDecodeBHist (ruleOneTenGliderCatalogEventAtDefault 5 ef))
      (ruleOneTenGliderCatalogDecodeBHist (ruleOneTenGliderCatalogEventAtDefault 7 ef))
      (ruleOneTenGliderCatalogDecodeBHist (ruleOneTenGliderCatalogEventAtDefault 9 ef))
      (ruleOneTenGliderCatalogDecodeBHist (ruleOneTenGliderCatalogEventAtDefault 11 ef))
      (ruleOneTenGliderCatalogDecodeBHist (ruleOneTenGliderCatalogEventAtDefault 13 ef))
      (ruleOneTenGliderCatalogDecodeBHist (ruleOneTenGliderCatalogEventAtDefault 15 ef))
      (ruleOneTenGliderCatalogDecodeBHist (ruleOneTenGliderCatalogEventAtDefault 17 ef)))

private theorem RuleOneTenGliderCatalogTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RuleOneTenGliderCatalogUp,
      ruleOneTenGliderCatalogFromEventFlow (ruleOneTenGliderCatalogToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R W G P D H C K N =>
      change
        some
          (RuleOneTenGliderCatalogUp.mk
            (ruleOneTenGliderCatalogDecodeBHist (ruleOneTenGliderCatalogEncodeBHist R))
            (ruleOneTenGliderCatalogDecodeBHist (ruleOneTenGliderCatalogEncodeBHist W))
            (ruleOneTenGliderCatalogDecodeBHist (ruleOneTenGliderCatalogEncodeBHist G))
            (ruleOneTenGliderCatalogDecodeBHist (ruleOneTenGliderCatalogEncodeBHist P))
            (ruleOneTenGliderCatalogDecodeBHist (ruleOneTenGliderCatalogEncodeBHist D))
            (ruleOneTenGliderCatalogDecodeBHist (ruleOneTenGliderCatalogEncodeBHist H))
            (ruleOneTenGliderCatalogDecodeBHist (ruleOneTenGliderCatalogEncodeBHist C))
            (ruleOneTenGliderCatalogDecodeBHist (ruleOneTenGliderCatalogEncodeBHist K))
            (ruleOneTenGliderCatalogDecodeBHist (ruleOneTenGliderCatalogEncodeBHist N))) =
          some (RuleOneTenGliderCatalogUp.mk R W G P D H C K N)
      rw [RuleOneTenGliderCatalogTasteGate_single_carrier_alignment_decode R,
        RuleOneTenGliderCatalogTasteGate_single_carrier_alignment_decode W,
        RuleOneTenGliderCatalogTasteGate_single_carrier_alignment_decode G,
        RuleOneTenGliderCatalogTasteGate_single_carrier_alignment_decode P,
        RuleOneTenGliderCatalogTasteGate_single_carrier_alignment_decode D,
        RuleOneTenGliderCatalogTasteGate_single_carrier_alignment_decode H,
        RuleOneTenGliderCatalogTasteGate_single_carrier_alignment_decode C,
        RuleOneTenGliderCatalogTasteGate_single_carrier_alignment_decode K,
        RuleOneTenGliderCatalogTasteGate_single_carrier_alignment_decode N]

private theorem RuleOneTenGliderCatalogTasteGate_single_carrier_alignment_injective
    {x y : RuleOneTenGliderCatalogUp} :
    ruleOneTenGliderCatalogToEventFlow x = ruleOneTenGliderCatalogToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ruleOneTenGliderCatalogFromEventFlow (ruleOneTenGliderCatalogToEventFlow x) =
        ruleOneTenGliderCatalogFromEventFlow (ruleOneTenGliderCatalogToEventFlow y) :=
    congrArg ruleOneTenGliderCatalogFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RuleOneTenGliderCatalogTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RuleOneTenGliderCatalogTasteGate_single_carrier_alignment_round_trip y)))

private theorem RuleOneTenGliderCatalogTasteGate_single_carrier_alignment_fields :
    ∀ x y : RuleOneTenGliderCatalogUp,
      ruleOneTenGliderCatalogFields x = ruleOneTenGliderCatalogFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ W₁ G₁ P₁ D₁ H₁ C₁ K₁ N₁ =>
      cases y with
      | mk R₂ W₂ G₂ P₂ D₂ H₂ C₂ K₂ N₂ =>
          cases hfields
          rfl

instance ruleOneTenGliderCatalogBHistCarrier : BHistCarrier RuleOneTenGliderCatalogUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ruleOneTenGliderCatalogToEventFlow
  fromEventFlow := ruleOneTenGliderCatalogFromEventFlow

instance ruleOneTenGliderCatalogChapterTasteGate :
    ChapterTasteGate RuleOneTenGliderCatalogUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change ruleOneTenGliderCatalogFromEventFlow (ruleOneTenGliderCatalogToEventFlow x) =
      some x
    exact RuleOneTenGliderCatalogTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RuleOneTenGliderCatalogTasteGate_single_carrier_alignment_injective heq)

instance ruleOneTenGliderCatalogFieldFaithful :
    FieldFaithful RuleOneTenGliderCatalogUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := ruleOneTenGliderCatalogFields
  field_faithful := RuleOneTenGliderCatalogTasteGate_single_carrier_alignment_fields

instance ruleOneTenGliderCatalogNontrivial : Nontrivial RuleOneTenGliderCatalogUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RuleOneTenGliderCatalogUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RuleOneTenGliderCatalogUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RuleOneTenGliderCatalogUp :=
  -- BEDC touchpoint anchor: BHist BMark
  ruleOneTenGliderCatalogChapterTasteGate

theorem RuleOneTenGliderCatalogTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      ruleOneTenGliderCatalogDecodeBHist (ruleOneTenGliderCatalogEncodeBHist h) = h) ∧
      ruleOneTenGliderCatalogEncodeBHist BHist.Empty = ([] : List BMark) ∧
        (∀ x y : RuleOneTenGliderCatalogUp,
          ruleOneTenGliderCatalogFields x = ruleOneTenGliderCatalogFields y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨RuleOneTenGliderCatalogTasteGate_single_carrier_alignment_decode,
      rfl,
      RuleOneTenGliderCatalogTasteGate_single_carrier_alignment_fields⟩

end BEDC.Derived.RuleOneTenGliderCatalogUp.TasteGate
