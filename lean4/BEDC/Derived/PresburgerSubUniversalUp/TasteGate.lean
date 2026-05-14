import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PresburgerSubUniversalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PresburgerSubUniversalUp : Type where
  | mk :
      (syntaxRow additive quantifier decision closure transport replay provenance name : BHist) →
      PresburgerSubUniversalUp
  deriving DecidableEq

def presburgerSubUniversalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: presburgerSubUniversalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: presburgerSubUniversalEncodeBHist h

def presburgerSubUniversalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (presburgerSubUniversalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (presburgerSubUniversalDecodeBHist tail)

private theorem presburgerSubUniversalDecodeEncodeBHist :
    ∀ h : BHist,
      presburgerSubUniversalDecodeBHist
        (presburgerSubUniversalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def presburgerSubUniversalFields :
    PresburgerSubUniversalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PresburgerSubUniversalUp.mk syntaxRow additive quantifier decision closure transport replay
      provenance name =>
      [syntaxRow, additive, quantifier, decision, closure, transport, replay, provenance, name]

def presburgerSubUniversalToEventFlow :
    PresburgerSubUniversalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (presburgerSubUniversalFields x).map presburgerSubUniversalEncodeBHist

def presburgerSubUniversalFromEventFlow :
    EventFlow → Option PresburgerSubUniversalUp
  -- BEDC touchpoint anchor: BHist BMark
  | [syntaxRow, additive, quantifier, decision, closure, transport, replay, provenance, name] =>
      some
        (PresburgerSubUniversalUp.mk
          (presburgerSubUniversalDecodeBHist syntaxRow)
          (presburgerSubUniversalDecodeBHist additive)
          (presburgerSubUniversalDecodeBHist quantifier)
          (presburgerSubUniversalDecodeBHist decision)
          (presburgerSubUniversalDecodeBHist closure)
          (presburgerSubUniversalDecodeBHist transport)
          (presburgerSubUniversalDecodeBHist replay)
          (presburgerSubUniversalDecodeBHist provenance)
          (presburgerSubUniversalDecodeBHist name))
  | _ => none

private theorem presburgerSubUniversal_round_trip :
    ∀ x : PresburgerSubUniversalUp,
      presburgerSubUniversalFromEventFlow
        (presburgerSubUniversalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk syntaxRow additive quantifier decision closure transport replay provenance name =>
      change
        some
          (PresburgerSubUniversalUp.mk
            (presburgerSubUniversalDecodeBHist
              (presburgerSubUniversalEncodeBHist syntaxRow))
            (presburgerSubUniversalDecodeBHist
              (presburgerSubUniversalEncodeBHist additive))
            (presburgerSubUniversalDecodeBHist
              (presburgerSubUniversalEncodeBHist quantifier))
            (presburgerSubUniversalDecodeBHist
              (presburgerSubUniversalEncodeBHist decision))
            (presburgerSubUniversalDecodeBHist
              (presburgerSubUniversalEncodeBHist closure))
            (presburgerSubUniversalDecodeBHist
              (presburgerSubUniversalEncodeBHist transport))
            (presburgerSubUniversalDecodeBHist
              (presburgerSubUniversalEncodeBHist replay))
            (presburgerSubUniversalDecodeBHist
              (presburgerSubUniversalEncodeBHist provenance))
            (presburgerSubUniversalDecodeBHist
              (presburgerSubUniversalEncodeBHist name))) =
          some
            (PresburgerSubUniversalUp.mk syntaxRow additive quantifier decision closure
              transport replay provenance name)
      rw [presburgerSubUniversalDecodeEncodeBHist syntaxRow,
        presburgerSubUniversalDecodeEncodeBHist additive,
        presburgerSubUniversalDecodeEncodeBHist quantifier,
        presburgerSubUniversalDecodeEncodeBHist decision,
        presburgerSubUniversalDecodeEncodeBHist closure,
        presburgerSubUniversalDecodeEncodeBHist transport,
        presburgerSubUniversalDecodeEncodeBHist replay,
        presburgerSubUniversalDecodeEncodeBHist provenance,
        presburgerSubUniversalDecodeEncodeBHist name]

private theorem presburgerSubUniversalToEventFlow_injective
    {x y : PresburgerSubUniversalUp} :
    presburgerSubUniversalToEventFlow x =
      presburgerSubUniversalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      presburgerSubUniversalFromEventFlow
          (presburgerSubUniversalToEventFlow x) =
        presburgerSubUniversalFromEventFlow
          (presburgerSubUniversalToEventFlow y) :=
    congrArg presburgerSubUniversalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (presburgerSubUniversal_round_trip x).symm
      (Eq.trans hread (presburgerSubUniversal_round_trip y)))

private theorem presburgerSubUniversal_fields_faithful :
    ∀ x y : PresburgerSubUniversalUp,
      presburgerSubUniversalFields x =
        presburgerSubUniversalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk syntaxRow₁ additive₁ quantifier₁ decision₁ closure₁ transport₁ replay₁
      provenance₁ name₁ =>
      cases y with
      | mk syntaxRow₂ additive₂ quantifier₂ decision₂ closure₂ transport₂ replay₂
          provenance₂ name₂ =>
          injection hfields with hsyntaxRow tail0
          injection tail0 with hadditive tail1
          injection tail1 with hquantifier tail2
          injection tail2 with hdecision tail3
          injection tail3 with hclosure tail4
          injection tail4 with htransport tail5
          injection tail5 with hreplay tail6
          injection tail6 with hprovenance tail7
          injection tail7 with hname _
          subst hsyntaxRow
          subst hadditive
          subst hquantifier
          subst hdecision
          subst hclosure
          subst htransport
          subst hreplay
          subst hprovenance
          subst hname
          rfl

instance presburgerSubUniversalBHistCarrier :
    BHistCarrier PresburgerSubUniversalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := presburgerSubUniversalToEventFlow
  fromEventFlow := presburgerSubUniversalFromEventFlow

instance presburgerSubUniversalChapterTasteGate :
    ChapterTasteGate PresburgerSubUniversalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change presburgerSubUniversalFromEventFlow
      (presburgerSubUniversalToEventFlow x) = some x
    exact presburgerSubUniversal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (presburgerSubUniversalToEventFlow_injective heq)

def taste_gate : ChapterTasteGate PresburgerSubUniversalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change presburgerSubUniversalFromEventFlow
      (presburgerSubUniversalToEventFlow x) = some x
    exact presburgerSubUniversal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (presburgerSubUniversalToEventFlow_injective heq)

instance presburgerSubUniversalFieldFaithful :
    FieldFaithful PresburgerSubUniversalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := presburgerSubUniversalFields
  field_faithful := presburgerSubUniversal_fields_faithful

instance presburgerSubUniversalNontrivial :
    Nontrivial PresburgerSubUniversalUp where
  witness_pair :=
    ⟨PresburgerSubUniversalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PresburgerSubUniversalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

end BEDC.Derived.PresburgerSubUniversalUp
