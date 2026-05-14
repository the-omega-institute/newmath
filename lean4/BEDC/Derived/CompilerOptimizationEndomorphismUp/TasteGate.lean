import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompilerOptimizationEndomorphismUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompilerOptimizationEndomorphismUp : Type where
  | mk :
      (source before after graph landing classifier frontier transport continuation provenance
        name : BHist) →
      CompilerOptimizationEndomorphismUp
  deriving DecidableEq

def compilerOptimizationEndomorphismEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compilerOptimizationEndomorphismEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compilerOptimizationEndomorphismEncodeBHist h

def compilerOptimizationEndomorphismDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compilerOptimizationEndomorphismDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compilerOptimizationEndomorphismDecodeBHist tail)

private theorem compilerOptimizationEndomorphism_decode_encode_bhist :
    ∀ h : BHist,
      compilerOptimizationEndomorphismDecodeBHist
        (compilerOptimizationEndomorphismEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def compilerOptimizationEndomorphismFields :
    CompilerOptimizationEndomorphismUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompilerOptimizationEndomorphismUp.mk source before after graph landing classifier frontier
      transport continuation provenance name =>
      [source, before, after, graph, landing, classifier, frontier, transport, continuation,
        provenance, name]

def compilerOptimizationEndomorphismToEventFlow :
    CompilerOptimizationEndomorphismUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompilerOptimizationEndomorphismUp.mk source before after graph landing classifier frontier
      transport continuation provenance name =>
      [[BMark.b0],
        compilerOptimizationEndomorphismEncodeBHist source,
        [BMark.b1, BMark.b0],
        compilerOptimizationEndomorphismEncodeBHist before,
        [BMark.b1, BMark.b1, BMark.b0],
        compilerOptimizationEndomorphismEncodeBHist after,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compilerOptimizationEndomorphismEncodeBHist graph,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compilerOptimizationEndomorphismEncodeBHist landing,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compilerOptimizationEndomorphismEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compilerOptimizationEndomorphismEncodeBHist frontier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        compilerOptimizationEndomorphismEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        compilerOptimizationEndomorphismEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        compilerOptimizationEndomorphismEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compilerOptimizationEndomorphismEncodeBHist name]

def compilerOptimizationEndomorphismFromEventFlow :
    EventFlow → Option CompilerOptimizationEndomorphismUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | source :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | before :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | after :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | graph :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | landing :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | classifier :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | frontier :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transport :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | continuation :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | provenance :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | name :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (CompilerOptimizationEndomorphismUp.mk
                                                                                                  (compilerOptimizationEndomorphismDecodeBHist
                                                                                                    source)
                                                                                                  (compilerOptimizationEndomorphismDecodeBHist
                                                                                                    before)
                                                                                                  (compilerOptimizationEndomorphismDecodeBHist
                                                                                                    after)
                                                                                                  (compilerOptimizationEndomorphismDecodeBHist
                                                                                                    graph)
                                                                                                  (compilerOptimizationEndomorphismDecodeBHist
                                                                                                    landing)
                                                                                                  (compilerOptimizationEndomorphismDecodeBHist
                                                                                                    classifier)
                                                                                                  (compilerOptimizationEndomorphismDecodeBHist
                                                                                                    frontier)
                                                                                                  (compilerOptimizationEndomorphismDecodeBHist
                                                                                                    transport)
                                                                                                  (compilerOptimizationEndomorphismDecodeBHist
                                                                                                    continuation)
                                                                                                  (compilerOptimizationEndomorphismDecodeBHist
                                                                                                    provenance)
                                                                                                  (compilerOptimizationEndomorphismDecodeBHist
                                                                                                    name))
                                                                                          | _ :: _ => none

private theorem compilerOptimizationEndomorphism_round_trip :
    ∀ x : CompilerOptimizationEndomorphismUp,
      compilerOptimizationEndomorphismFromEventFlow
        (compilerOptimizationEndomorphismToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source before after graph landing classifier frontier transport continuation provenance
      name =>
      change
        some
          (CompilerOptimizationEndomorphismUp.mk
            (compilerOptimizationEndomorphismDecodeBHist
              (compilerOptimizationEndomorphismEncodeBHist source))
            (compilerOptimizationEndomorphismDecodeBHist
              (compilerOptimizationEndomorphismEncodeBHist before))
            (compilerOptimizationEndomorphismDecodeBHist
              (compilerOptimizationEndomorphismEncodeBHist after))
            (compilerOptimizationEndomorphismDecodeBHist
              (compilerOptimizationEndomorphismEncodeBHist graph))
            (compilerOptimizationEndomorphismDecodeBHist
              (compilerOptimizationEndomorphismEncodeBHist landing))
            (compilerOptimizationEndomorphismDecodeBHist
              (compilerOptimizationEndomorphismEncodeBHist classifier))
            (compilerOptimizationEndomorphismDecodeBHist
              (compilerOptimizationEndomorphismEncodeBHist frontier))
            (compilerOptimizationEndomorphismDecodeBHist
              (compilerOptimizationEndomorphismEncodeBHist transport))
            (compilerOptimizationEndomorphismDecodeBHist
              (compilerOptimizationEndomorphismEncodeBHist continuation))
            (compilerOptimizationEndomorphismDecodeBHist
              (compilerOptimizationEndomorphismEncodeBHist provenance))
            (compilerOptimizationEndomorphismDecodeBHist
              (compilerOptimizationEndomorphismEncodeBHist name))) =
          some
            (CompilerOptimizationEndomorphismUp.mk source before after graph landing classifier
              frontier transport continuation provenance name)
      rw [compilerOptimizationEndomorphism_decode_encode_bhist source,
        compilerOptimizationEndomorphism_decode_encode_bhist before,
        compilerOptimizationEndomorphism_decode_encode_bhist after,
        compilerOptimizationEndomorphism_decode_encode_bhist graph,
        compilerOptimizationEndomorphism_decode_encode_bhist landing,
        compilerOptimizationEndomorphism_decode_encode_bhist classifier,
        compilerOptimizationEndomorphism_decode_encode_bhist frontier,
        compilerOptimizationEndomorphism_decode_encode_bhist transport,
        compilerOptimizationEndomorphism_decode_encode_bhist continuation,
        compilerOptimizationEndomorphism_decode_encode_bhist provenance,
        compilerOptimizationEndomorphism_decode_encode_bhist name]

private theorem compilerOptimizationEndomorphismToEventFlow_injective
    {x y : CompilerOptimizationEndomorphismUp} :
    compilerOptimizationEndomorphismToEventFlow x =
      compilerOptimizationEndomorphismToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compilerOptimizationEndomorphismFromEventFlow
          (compilerOptimizationEndomorphismToEventFlow x) =
        compilerOptimizationEndomorphismFromEventFlow
          (compilerOptimizationEndomorphismToEventFlow y) :=
    congrArg compilerOptimizationEndomorphismFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compilerOptimizationEndomorphism_round_trip x).symm
      (Eq.trans hread (compilerOptimizationEndomorphism_round_trip y)))

private theorem CompilerOptimizationEndomorphismTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CompilerOptimizationEndomorphismUp,
      compilerOptimizationEndomorphismFields x =
        compilerOptimizationEndomorphismFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source before after graph landing classifier frontier transport continuation provenance name =>
      cases y with
      | mk source' before' after' graph' landing' classifier' frontier' transport' continuation'
          provenance' name' =>
          cases hfields
          rfl

instance compilerOptimizationEndomorphismBHistCarrier :
    BHistCarrier CompilerOptimizationEndomorphismUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compilerOptimizationEndomorphismToEventFlow
  fromEventFlow := compilerOptimizationEndomorphismFromEventFlow

instance compilerOptimizationEndomorphismChapterTasteGate :
    ChapterTasteGate CompilerOptimizationEndomorphismUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compilerOptimizationEndomorphismFromEventFlow
        (compilerOptimizationEndomorphismToEventFlow x) = some x
    exact compilerOptimizationEndomorphism_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compilerOptimizationEndomorphismToEventFlow_injective heq)

instance compilerOptimizationEndomorphismFieldFaithful :
    FieldFaithful CompilerOptimizationEndomorphismUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compilerOptimizationEndomorphismFields
  field_faithful :=
    CompilerOptimizationEndomorphismTasteGate_single_carrier_alignment_field_faithful

theorem CompilerOptimizationEndomorphismTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compilerOptimizationEndomorphismDecodeBHist
        (compilerOptimizationEndomorphismEncodeBHist h) = h) ∧
      (∀ x : CompilerOptimizationEndomorphismUp,
        compilerOptimizationEndomorphismFromEventFlow
          (compilerOptimizationEndomorphismToEventFlow x) = some x) ∧
        (∀ x y : CompilerOptimizationEndomorphismUp,
          compilerOptimizationEndomorphismToEventFlow x =
            compilerOptimizationEndomorphismToEventFlow y → x = y) ∧
          compilerOptimizationEndomorphismEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact compilerOptimizationEndomorphism_decode_encode_bhist
  · constructor
    · exact compilerOptimizationEndomorphism_round_trip
    · constructor
      · intro x y heq
        exact compilerOptimizationEndomorphismToEventFlow_injective heq
      · rfl

end BEDC.Derived.CompilerOptimizationEndomorphismUp
