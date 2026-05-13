import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LiteralASTEqualityBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LiteralASTEqualityBoundaryUp : Type where
  | mk :
      (ast literal boundary handoff classifier provenance name : BHist) →
      LiteralASTEqualityBoundaryUp
  deriving DecidableEq

def literalASTEqualityBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: literalASTEqualityBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: literalASTEqualityBoundaryEncodeBHist h

def literalASTEqualityBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (literalASTEqualityBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (literalASTEqualityBoundaryDecodeBHist tail)

private theorem literalASTEqualityBoundary_decode_encode_bhist :
    ∀ h : BHist,
      literalASTEqualityBoundaryDecodeBHist (literalASTEqualityBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def literalASTEqualityBoundaryToEventFlow : LiteralASTEqualityBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LiteralASTEqualityBoundaryUp.mk ast literal boundary handoff classifier provenance name =>
      [[BMark.b0],
        literalASTEqualityBoundaryEncodeBHist ast,
        [BMark.b1, BMark.b0],
        literalASTEqualityBoundaryEncodeBHist literal,
        [BMark.b1, BMark.b1, BMark.b0],
        literalASTEqualityBoundaryEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        literalASTEqualityBoundaryEncodeBHist handoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        literalASTEqualityBoundaryEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        literalASTEqualityBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        literalASTEqualityBoundaryEncodeBHist name]

def literalASTEqualityBoundaryFromEventFlow :
    EventFlow → Option LiteralASTEqualityBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | ast :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | literal :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | boundary :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | handoff :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | classifier :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | name :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (LiteralASTEqualityBoundaryUp.mk
                                                                  (literalASTEqualityBoundaryDecodeBHist
                                                                    ast)
                                                                  (literalASTEqualityBoundaryDecodeBHist
                                                                    literal)
                                                                  (literalASTEqualityBoundaryDecodeBHist
                                                                    boundary)
                                                                  (literalASTEqualityBoundaryDecodeBHist
                                                                    handoff)
                                                                  (literalASTEqualityBoundaryDecodeBHist
                                                                    classifier)
                                                                  (literalASTEqualityBoundaryDecodeBHist
                                                                    provenance)
                                                                  (literalASTEqualityBoundaryDecodeBHist
                                                                    name))
                                                          | _ :: _ => none

private theorem literalASTEqualityBoundary_round_trip :
    ∀ x : LiteralASTEqualityBoundaryUp,
      literalASTEqualityBoundaryFromEventFlow (literalASTEqualityBoundaryToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk ast literal boundary handoff classifier provenance name =>
      change
        some
          (LiteralASTEqualityBoundaryUp.mk
            (literalASTEqualityBoundaryDecodeBHist
              (literalASTEqualityBoundaryEncodeBHist ast))
            (literalASTEqualityBoundaryDecodeBHist
              (literalASTEqualityBoundaryEncodeBHist literal))
            (literalASTEqualityBoundaryDecodeBHist
              (literalASTEqualityBoundaryEncodeBHist boundary))
            (literalASTEqualityBoundaryDecodeBHist
              (literalASTEqualityBoundaryEncodeBHist handoff))
            (literalASTEqualityBoundaryDecodeBHist
              (literalASTEqualityBoundaryEncodeBHist classifier))
            (literalASTEqualityBoundaryDecodeBHist
              (literalASTEqualityBoundaryEncodeBHist provenance))
            (literalASTEqualityBoundaryDecodeBHist
              (literalASTEqualityBoundaryEncodeBHist name))) =
          some
            (LiteralASTEqualityBoundaryUp.mk ast literal boundary handoff classifier provenance
              name)
      rw [literalASTEqualityBoundary_decode_encode_bhist ast,
        literalASTEqualityBoundary_decode_encode_bhist literal,
        literalASTEqualityBoundary_decode_encode_bhist boundary,
        literalASTEqualityBoundary_decode_encode_bhist handoff,
        literalASTEqualityBoundary_decode_encode_bhist classifier,
        literalASTEqualityBoundary_decode_encode_bhist provenance,
        literalASTEqualityBoundary_decode_encode_bhist name]

private theorem literalASTEqualityBoundaryToEventFlow_injective
    {x y : LiteralASTEqualityBoundaryUp} :
    literalASTEqualityBoundaryToEventFlow x =
      literalASTEqualityBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      literalASTEqualityBoundaryFromEventFlow (literalASTEqualityBoundaryToEventFlow x) =
        literalASTEqualityBoundaryFromEventFlow (literalASTEqualityBoundaryToEventFlow y) :=
    congrArg literalASTEqualityBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (literalASTEqualityBoundary_round_trip x).symm
      (Eq.trans hread (literalASTEqualityBoundary_round_trip y)))

instance literalASTEqualityBoundaryBHistCarrier :
    BHistCarrier LiteralASTEqualityBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := literalASTEqualityBoundaryToEventFlow
  fromEventFlow := literalASTEqualityBoundaryFromEventFlow

instance literalASTEqualityBoundaryChapterTasteGate :
    ChapterTasteGate LiteralASTEqualityBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change literalASTEqualityBoundaryFromEventFlow (literalASTEqualityBoundaryToEventFlow x) =
      some x
    exact literalASTEqualityBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (literalASTEqualityBoundaryToEventFlow_injective heq)

instance literalASTEqualityBoundaryFieldFaithful :
    FieldFaithful LiteralASTEqualityBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | LiteralASTEqualityBoundaryUp.mk ast literal boundary handoff classifier provenance name =>
        [ast, literal, boundary, handoff, classifier, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk ast₁ literal₁ boundary₁ handoff₁ classifier₁ provenance₁ name₁ =>
        cases y with
        | mk ast₂ literal₂ boundary₂ handoff₂ classifier₂ provenance₂ name₂ =>
            simp only [] at h
            injection h with hAst hRest₁
            injection hRest₁ with hLiteral hRest₂
            injection hRest₂ with hBoundary hRest₃
            injection hRest₃ with hHandoff hRest₄
            injection hRest₄ with hClassifier hRest₅
            injection hRest₅ with hProvenance hRest₆
            injection hRest₆ with hName _
            subst hAst
            subst hLiteral
            subst hBoundary
            subst hHandoff
            subst hClassifier
            subst hProvenance
            subst hName
            rfl

instance literalASTEqualityBoundaryNontrivial :
    Nontrivial LiteralASTEqualityBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LiteralASTEqualityBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      LiteralASTEqualityBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem LiteralASTEqualityBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist, literalASTEqualityBoundaryDecodeBHist
      (literalASTEqualityBoundaryEncodeBHist h) = h) ∧
      (∀ x : LiteralASTEqualityBoundaryUp,
        literalASTEqualityBoundaryFromEventFlow (literalASTEqualityBoundaryToEventFlow x) =
          some x) ∧
        (∀ x y : LiteralASTEqualityBoundaryUp,
          literalASTEqualityBoundaryToEventFlow x = literalASTEqualityBoundaryToEventFlow y ->
            x = y) ∧
          literalASTEqualityBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact literalASTEqualityBoundary_decode_encode_bhist
  · constructor
    · exact literalASTEqualityBoundary_round_trip
    · constructor
      · intro x y heq
        exact literalASTEqualityBoundaryToEventFlow_injective heq
      · rfl

end BEDC.Derived.LiteralASTEqualityBoundaryUp
