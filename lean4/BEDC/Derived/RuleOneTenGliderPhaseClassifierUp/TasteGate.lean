import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RuleOneTenGliderPhaseClassifierUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RuleOneTenGliderPhaseClassifierUp : Type where
  | mk (R W K O M E L H C P N : BHist) : RuleOneTenGliderPhaseClassifierUp
  deriving DecidableEq

def ruleOneTenGliderPhaseClassifierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ruleOneTenGliderPhaseClassifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: ruleOneTenGliderPhaseClassifierEncodeBHist h

def ruleOneTenGliderPhaseClassifierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (ruleOneTenGliderPhaseClassifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (ruleOneTenGliderPhaseClassifierDecodeBHist tail)

private theorem RuleOneTenGliderPhaseClassifierTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      ruleOneTenGliderPhaseClassifierDecodeBHist
        (ruleOneTenGliderPhaseClassifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ruleOneTenGliderPhaseClassifierFields :
    RuleOneTenGliderPhaseClassifierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RuleOneTenGliderPhaseClassifierUp.mk R W K O M E L H C P N =>
      [R, W, K, O, M, E, L, H, C, P, N]

def ruleOneTenGliderPhaseClassifierToEventFlow :
    RuleOneTenGliderPhaseClassifierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RuleOneTenGliderPhaseClassifierUp.mk R W K O M E L H C P N =>
      [[BMark.b0],
        ruleOneTenGliderPhaseClassifierEncodeBHist R,
        [BMark.b1, BMark.b0],
        ruleOneTenGliderPhaseClassifierEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b0],
        ruleOneTenGliderPhaseClassifierEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        ruleOneTenGliderPhaseClassifierEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        ruleOneTenGliderPhaseClassifierEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        ruleOneTenGliderPhaseClassifierEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        ruleOneTenGliderPhaseClassifierEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        ruleOneTenGliderPhaseClassifierEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        ruleOneTenGliderPhaseClassifierEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        ruleOneTenGliderPhaseClassifierEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        ruleOneTenGliderPhaseClassifierEncodeBHist N]

private def ruleOneTenGliderPhaseClassifierEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      ruleOneTenGliderPhaseClassifierEventAtDefault index rest

def ruleOneTenGliderPhaseClassifierFromEventFlow
    (ef : EventFlow) : Option RuleOneTenGliderPhaseClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RuleOneTenGliderPhaseClassifierUp.mk
      (ruleOneTenGliderPhaseClassifierDecodeBHist
        (ruleOneTenGliderPhaseClassifierEventAtDefault 1 ef))
      (ruleOneTenGliderPhaseClassifierDecodeBHist
        (ruleOneTenGliderPhaseClassifierEventAtDefault 3 ef))
      (ruleOneTenGliderPhaseClassifierDecodeBHist
        (ruleOneTenGliderPhaseClassifierEventAtDefault 5 ef))
      (ruleOneTenGliderPhaseClassifierDecodeBHist
        (ruleOneTenGliderPhaseClassifierEventAtDefault 7 ef))
      (ruleOneTenGliderPhaseClassifierDecodeBHist
        (ruleOneTenGliderPhaseClassifierEventAtDefault 9 ef))
      (ruleOneTenGliderPhaseClassifierDecodeBHist
        (ruleOneTenGliderPhaseClassifierEventAtDefault 11 ef))
      (ruleOneTenGliderPhaseClassifierDecodeBHist
        (ruleOneTenGliderPhaseClassifierEventAtDefault 13 ef))
      (ruleOneTenGliderPhaseClassifierDecodeBHist
        (ruleOneTenGliderPhaseClassifierEventAtDefault 15 ef))
      (ruleOneTenGliderPhaseClassifierDecodeBHist
        (ruleOneTenGliderPhaseClassifierEventAtDefault 17 ef))
      (ruleOneTenGliderPhaseClassifierDecodeBHist
        (ruleOneTenGliderPhaseClassifierEventAtDefault 19 ef))
      (ruleOneTenGliderPhaseClassifierDecodeBHist
        (ruleOneTenGliderPhaseClassifierEventAtDefault 21 ef)))

private theorem RuleOneTenGliderPhaseClassifierTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RuleOneTenGliderPhaseClassifierUp,
      ruleOneTenGliderPhaseClassifierFromEventFlow
        (ruleOneTenGliderPhaseClassifierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R W K O M E L H C P N =>
      change
        some
          (RuleOneTenGliderPhaseClassifierUp.mk
            (ruleOneTenGliderPhaseClassifierDecodeBHist
              (ruleOneTenGliderPhaseClassifierEncodeBHist R))
            (ruleOneTenGliderPhaseClassifierDecodeBHist
              (ruleOneTenGliderPhaseClassifierEncodeBHist W))
            (ruleOneTenGliderPhaseClassifierDecodeBHist
              (ruleOneTenGliderPhaseClassifierEncodeBHist K))
            (ruleOneTenGliderPhaseClassifierDecodeBHist
              (ruleOneTenGliderPhaseClassifierEncodeBHist O))
            (ruleOneTenGliderPhaseClassifierDecodeBHist
              (ruleOneTenGliderPhaseClassifierEncodeBHist M))
            (ruleOneTenGliderPhaseClassifierDecodeBHist
              (ruleOneTenGliderPhaseClassifierEncodeBHist E))
            (ruleOneTenGliderPhaseClassifierDecodeBHist
              (ruleOneTenGliderPhaseClassifierEncodeBHist L))
            (ruleOneTenGliderPhaseClassifierDecodeBHist
              (ruleOneTenGliderPhaseClassifierEncodeBHist H))
            (ruleOneTenGliderPhaseClassifierDecodeBHist
              (ruleOneTenGliderPhaseClassifierEncodeBHist C))
            (ruleOneTenGliderPhaseClassifierDecodeBHist
              (ruleOneTenGliderPhaseClassifierEncodeBHist P))
            (ruleOneTenGliderPhaseClassifierDecodeBHist
              (ruleOneTenGliderPhaseClassifierEncodeBHist N))) =
          some (RuleOneTenGliderPhaseClassifierUp.mk R W K O M E L H C P N)
      rw [RuleOneTenGliderPhaseClassifierTasteGate_single_carrier_alignment_decode R,
        RuleOneTenGliderPhaseClassifierTasteGate_single_carrier_alignment_decode W,
        RuleOneTenGliderPhaseClassifierTasteGate_single_carrier_alignment_decode K,
        RuleOneTenGliderPhaseClassifierTasteGate_single_carrier_alignment_decode O,
        RuleOneTenGliderPhaseClassifierTasteGate_single_carrier_alignment_decode M,
        RuleOneTenGliderPhaseClassifierTasteGate_single_carrier_alignment_decode E,
        RuleOneTenGliderPhaseClassifierTasteGate_single_carrier_alignment_decode L,
        RuleOneTenGliderPhaseClassifierTasteGate_single_carrier_alignment_decode H,
        RuleOneTenGliderPhaseClassifierTasteGate_single_carrier_alignment_decode C,
        RuleOneTenGliderPhaseClassifierTasteGate_single_carrier_alignment_decode P,
        RuleOneTenGliderPhaseClassifierTasteGate_single_carrier_alignment_decode N]

private theorem RuleOneTenGliderPhaseClassifierTasteGate_single_carrier_alignment_injective
    {x y : RuleOneTenGliderPhaseClassifierUp} :
    ruleOneTenGliderPhaseClassifierToEventFlow x =
        ruleOneTenGliderPhaseClassifierToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ruleOneTenGliderPhaseClassifierFromEventFlow
          (ruleOneTenGliderPhaseClassifierToEventFlow x) =
        ruleOneTenGliderPhaseClassifierFromEventFlow
          (ruleOneTenGliderPhaseClassifierToEventFlow y) :=
    congrArg ruleOneTenGliderPhaseClassifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RuleOneTenGliderPhaseClassifierTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RuleOneTenGliderPhaseClassifierTasteGate_single_carrier_alignment_round_trip y)))

private theorem RuleOneTenGliderPhaseClassifierTasteGate_single_carrier_alignment_fields :
    ∀ x y : RuleOneTenGliderPhaseClassifierUp,
      ruleOneTenGliderPhaseClassifierFields x =
          ruleOneTenGliderPhaseClassifierFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ W₁ K₁ O₁ M₁ E₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ W₂ K₂ O₂ M₂ E₂ L₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance ruleOneTenGliderPhaseClassifierBHistCarrier :
    BHistCarrier RuleOneTenGliderPhaseClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ruleOneTenGliderPhaseClassifierToEventFlow
  fromEventFlow := ruleOneTenGliderPhaseClassifierFromEventFlow

instance ruleOneTenGliderPhaseClassifierChapterTasteGate :
    ChapterTasteGate RuleOneTenGliderPhaseClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change ruleOneTenGliderPhaseClassifierFromEventFlow
      (ruleOneTenGliderPhaseClassifierToEventFlow x) = some x
    exact RuleOneTenGliderPhaseClassifierTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RuleOneTenGliderPhaseClassifierTasteGate_single_carrier_alignment_injective heq)

instance ruleOneTenGliderPhaseClassifierFieldFaithful :
    FieldFaithful RuleOneTenGliderPhaseClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := ruleOneTenGliderPhaseClassifierFields
  field_faithful := RuleOneTenGliderPhaseClassifierTasteGate_single_carrier_alignment_fields

instance ruleOneTenGliderPhaseClassifierNontrivial :
    Nontrivial RuleOneTenGliderPhaseClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RuleOneTenGliderPhaseClassifierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RuleOneTenGliderPhaseClassifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RuleOneTenGliderPhaseClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  ruleOneTenGliderPhaseClassifierChapterTasteGate

theorem RuleOneTenGliderPhaseClassifierTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      ruleOneTenGliderPhaseClassifierDecodeBHist
        (ruleOneTenGliderPhaseClassifierEncodeBHist h) = h) ∧
      ruleOneTenGliderPhaseClassifierEncodeBHist BHist.Empty = ([] : List BMark) ∧
        (∀ x y : RuleOneTenGliderPhaseClassifierUp,
          ruleOneTenGliderPhaseClassifierFields x =
              ruleOneTenGliderPhaseClassifierFields y →
            x = y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨RuleOneTenGliderPhaseClassifierTasteGate_single_carrier_alignment_decode,
      rfl,
      RuleOneTenGliderPhaseClassifierTasteGate_single_carrier_alignment_fields⟩

end BEDC.Derived.RuleOneTenGliderPhaseClassifierUp.TasteGate
