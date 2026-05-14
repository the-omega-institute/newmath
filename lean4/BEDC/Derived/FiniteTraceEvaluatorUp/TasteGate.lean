import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

/-!
# FiniteTraceEvaluatorUp TasteGate carrier.
-/

namespace BEDC.Derived.FiniteTraceEvaluatorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteTraceEvaluatorUp : Type where
  | mk : (input trace accepted validation transport route provenance name : BHist) →
      FiniteTraceEvaluatorUp
  deriving DecidableEq

def finiteTraceEvaluatorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteTraceEvaluatorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteTraceEvaluatorEncodeBHist h

def finiteTraceEvaluatorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteTraceEvaluatorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteTraceEvaluatorDecodeBHist tail)

private theorem finiteTraceEvaluatorDecodeEncodeBHist :
    ∀ h : BHist, finiteTraceEvaluatorDecodeBHist
      (finiteTraceEvaluatorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteTraceEvaluatorFields : FiniteTraceEvaluatorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteTraceEvaluatorUp.mk input trace accepted validation transport route provenance name =>
      [input, trace, accepted, validation, transport, route, provenance, name]

def finiteTraceEvaluatorToEventFlow : FiniteTraceEvaluatorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteTraceEvaluatorFields x).map finiteTraceEvaluatorEncodeBHist

def finiteTraceEvaluatorFromEventFlow : EventFlow → Option FiniteTraceEvaluatorUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | input :: rest0 =>
      match rest0 with
      | [] => none
      | trace :: rest1 =>
          match rest1 with
          | [] => none
          | accepted :: rest2 =>
              match rest2 with
              | [] => none
              | validation :: rest3 =>
                  match rest3 with
                  | [] => none
                  | transport :: rest4 =>
                      match rest4 with
                      | [] => none
                      | route :: rest5 =>
                          match rest5 with
                          | [] => none
                          | provenance :: rest6 =>
                              match rest6 with
                              | [] => none
                              | name :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (FiniteTraceEvaluatorUp.mk
                                          (finiteTraceEvaluatorDecodeBHist input)
                                          (finiteTraceEvaluatorDecodeBHist trace)
                                          (finiteTraceEvaluatorDecodeBHist accepted)
                                          (finiteTraceEvaluatorDecodeBHist validation)
                                          (finiteTraceEvaluatorDecodeBHist transport)
                                          (finiteTraceEvaluatorDecodeBHist route)
                                          (finiteTraceEvaluatorDecodeBHist provenance)
                                          (finiteTraceEvaluatorDecodeBHist name))
                                  | _ :: _ => none

private theorem finiteTraceEvaluator_round_trip :
    ∀ x : FiniteTraceEvaluatorUp,
      finiteTraceEvaluatorFromEventFlow
        (finiteTraceEvaluatorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk input trace accepted validation transport route provenance name =>
      change
        some
          (FiniteTraceEvaluatorUp.mk
            (finiteTraceEvaluatorDecodeBHist (finiteTraceEvaluatorEncodeBHist input))
            (finiteTraceEvaluatorDecodeBHist (finiteTraceEvaluatorEncodeBHist trace))
            (finiteTraceEvaluatorDecodeBHist (finiteTraceEvaluatorEncodeBHist accepted))
            (finiteTraceEvaluatorDecodeBHist (finiteTraceEvaluatorEncodeBHist validation))
            (finiteTraceEvaluatorDecodeBHist (finiteTraceEvaluatorEncodeBHist transport))
            (finiteTraceEvaluatorDecodeBHist (finiteTraceEvaluatorEncodeBHist route))
            (finiteTraceEvaluatorDecodeBHist (finiteTraceEvaluatorEncodeBHist provenance))
            (finiteTraceEvaluatorDecodeBHist (finiteTraceEvaluatorEncodeBHist name))) =
          some
            (FiniteTraceEvaluatorUp.mk input trace accepted validation transport route
              provenance name)
      rw [finiteTraceEvaluatorDecodeEncodeBHist input,
        finiteTraceEvaluatorDecodeEncodeBHist trace,
        finiteTraceEvaluatorDecodeEncodeBHist accepted,
        finiteTraceEvaluatorDecodeEncodeBHist validation,
        finiteTraceEvaluatorDecodeEncodeBHist transport,
        finiteTraceEvaluatorDecodeEncodeBHist route,
        finiteTraceEvaluatorDecodeEncodeBHist provenance,
        finiteTraceEvaluatorDecodeEncodeBHist name]

private theorem finiteTraceEvaluatorToEventFlow_injective
    {x y : FiniteTraceEvaluatorUp} :
    finiteTraceEvaluatorToEventFlow x = finiteTraceEvaluatorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteTraceEvaluatorFromEventFlow (finiteTraceEvaluatorToEventFlow x) =
        finiteTraceEvaluatorFromEventFlow (finiteTraceEvaluatorToEventFlow y) :=
    congrArg finiteTraceEvaluatorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteTraceEvaluator_round_trip x).symm
      (Eq.trans hread (finiteTraceEvaluator_round_trip y)))

private theorem finiteTraceEvaluator_fields_faithful :
    ∀ x y : FiniteTraceEvaluatorUp,
      finiteTraceEvaluatorFields x = finiteTraceEvaluatorFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk input₁ trace₁ accepted₁ validation₁ transport₁ route₁ provenance₁ name₁ =>
      cases y with
      | mk input₂ trace₂ accepted₂ validation₂ transport₂ route₂ provenance₂ name₂ =>
          injection hfields with hinput tail0
          injection tail0 with htrace tail1
          injection tail1 with haccepted tail2
          injection tail2 with hvalidation tail3
          injection tail3 with htransport tail4
          injection tail4 with hroute tail5
          injection tail5 with hprovenance tail6
          injection tail6 with hname _
          subst hinput
          subst htrace
          subst haccepted
          subst hvalidation
          subst htransport
          subst hroute
          subst hprovenance
          subst hname
          rfl

instance finiteTraceEvaluatorBHistCarrier : BHistCarrier FiniteTraceEvaluatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteTraceEvaluatorToEventFlow
  fromEventFlow := finiteTraceEvaluatorFromEventFlow

instance finiteTraceEvaluatorChapterTasteGate :
    ChapterTasteGate FiniteTraceEvaluatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteTraceEvaluatorFromEventFlow
      (finiteTraceEvaluatorToEventFlow x) = some x
    exact finiteTraceEvaluator_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteTraceEvaluatorToEventFlow_injective heq)

instance finiteTraceEvaluatorFieldFaithful : FieldFaithful FiniteTraceEvaluatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteTraceEvaluatorFields
  field_faithful := finiteTraceEvaluator_fields_faithful

def taste_gate : ChapterTasteGate FiniteTraceEvaluatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteTraceEvaluatorFromEventFlow
      (finiteTraceEvaluatorToEventFlow x) = some x
    exact finiteTraceEvaluator_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteTraceEvaluatorToEventFlow_injective heq)

theorem FiniteTraceEvaluatorTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteTraceEvaluatorDecodeBHist
      (finiteTraceEvaluatorEncodeBHist h) = h) ∧
      (∀ x : FiniteTraceEvaluatorUp,
        finiteTraceEvaluatorFromEventFlow (finiteTraceEvaluatorToEventFlow x) = some x) ∧
        (∀ x y : FiniteTraceEvaluatorUp,
          finiteTraceEvaluatorToEventFlow x = finiteTraceEvaluatorToEventFlow y -> x = y) ∧
          finiteTraceEvaluatorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact finiteTraceEvaluatorDecodeEncodeBHist
  · constructor
    · exact finiteTraceEvaluator_round_trip
    · constructor
      · intro x y heq
        exact finiteTraceEvaluatorToEventFlow_injective heq
      · rfl

end BEDC.Derived.FiniteTraceEvaluatorUp
