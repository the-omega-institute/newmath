import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GeneratorLocalInductionBoundaryUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GeneratorLocalInductionBoundaryUp : Type where
  | mk
      (generatorDomain eliminatorLocality inductionLedger freeFloatingRefusal transport
        continuation provenance name : BHist) :
      GeneratorLocalInductionBoundaryUp
  deriving DecidableEq

def generatorLocalInductionBoundaryEncodeBHist : BHist -> RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: generatorLocalInductionBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: generatorLocalInductionBoundaryEncodeBHist h

def generatorLocalInductionBoundaryDecodeBHist : RawEvent -> BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (generatorLocalInductionBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (generatorLocalInductionBoundaryDecodeBHist tail)

private theorem generatorLocalInductionBoundaryDecode_encode_bhist :
    forall h : BHist,
      generatorLocalInductionBoundaryDecodeBHist
        (generatorLocalInductionBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def generatorLocalInductionBoundaryToEventFlow :
    GeneratorLocalInductionBoundaryUp -> EventFlow
  | GeneratorLocalInductionBoundaryUp.mk generatorDomain eliminatorLocality inductionLedger
      freeFloatingRefusal transport continuation provenance name =>
      [[BMark.b0],
        generatorLocalInductionBoundaryEncodeBHist generatorDomain,
        [BMark.b1, BMark.b0],
        generatorLocalInductionBoundaryEncodeBHist eliminatorLocality,
        [BMark.b1, BMark.b1, BMark.b0],
        generatorLocalInductionBoundaryEncodeBHist inductionLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        generatorLocalInductionBoundaryEncodeBHist freeFloatingRefusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        generatorLocalInductionBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        generatorLocalInductionBoundaryEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        generatorLocalInductionBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        generatorLocalInductionBoundaryEncodeBHist name]

def generatorLocalInductionBoundaryFromEventFlow :
    EventFlow -> Option GeneratorLocalInductionBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | generatorDomain :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | eliminatorLocality :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | inductionLedger :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | freeFloatingRefusal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | continuation :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | name :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (GeneratorLocalInductionBoundaryUp.mk
                                                                          (generatorLocalInductionBoundaryDecodeBHist
                                                                            generatorDomain)
                                                                          (generatorLocalInductionBoundaryDecodeBHist
                                                                            eliminatorLocality)
                                                                          (generatorLocalInductionBoundaryDecodeBHist
                                                                            inductionLedger)
                                                                          (generatorLocalInductionBoundaryDecodeBHist
                                                                            freeFloatingRefusal)
                                                                          (generatorLocalInductionBoundaryDecodeBHist
                                                                            transport)
                                                                          (generatorLocalInductionBoundaryDecodeBHist
                                                                            continuation)
                                                                          (generatorLocalInductionBoundaryDecodeBHist
                                                                            provenance)
                                                                          (generatorLocalInductionBoundaryDecodeBHist
                                                                            name))
                                                                  | _ :: _ => none

private theorem generatorLocalInductionBoundary_round_trip :
    forall x : GeneratorLocalInductionBoundaryUp,
      generatorLocalInductionBoundaryFromEventFlow
        (generatorLocalInductionBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk generatorDomain eliminatorLocality inductionLedger freeFloatingRefusal transport
      continuation provenance name =>
      change
        some
          (GeneratorLocalInductionBoundaryUp.mk
            (generatorLocalInductionBoundaryDecodeBHist
              (generatorLocalInductionBoundaryEncodeBHist generatorDomain))
            (generatorLocalInductionBoundaryDecodeBHist
              (generatorLocalInductionBoundaryEncodeBHist eliminatorLocality))
            (generatorLocalInductionBoundaryDecodeBHist
              (generatorLocalInductionBoundaryEncodeBHist inductionLedger))
            (generatorLocalInductionBoundaryDecodeBHist
              (generatorLocalInductionBoundaryEncodeBHist freeFloatingRefusal))
            (generatorLocalInductionBoundaryDecodeBHist
              (generatorLocalInductionBoundaryEncodeBHist transport))
            (generatorLocalInductionBoundaryDecodeBHist
              (generatorLocalInductionBoundaryEncodeBHist continuation))
            (generatorLocalInductionBoundaryDecodeBHist
              (generatorLocalInductionBoundaryEncodeBHist provenance))
            (generatorLocalInductionBoundaryDecodeBHist
              (generatorLocalInductionBoundaryEncodeBHist name))) =
          some
            (GeneratorLocalInductionBoundaryUp.mk generatorDomain eliminatorLocality
              inductionLedger freeFloatingRefusal transport continuation provenance name)
      rw [generatorLocalInductionBoundaryDecode_encode_bhist generatorDomain,
        generatorLocalInductionBoundaryDecode_encode_bhist eliminatorLocality,
        generatorLocalInductionBoundaryDecode_encode_bhist inductionLedger,
        generatorLocalInductionBoundaryDecode_encode_bhist freeFloatingRefusal,
        generatorLocalInductionBoundaryDecode_encode_bhist transport,
        generatorLocalInductionBoundaryDecode_encode_bhist continuation,
        generatorLocalInductionBoundaryDecode_encode_bhist provenance,
        generatorLocalInductionBoundaryDecode_encode_bhist name]

private theorem generatorLocalInductionBoundaryToEventFlow_injective
    {x y : GeneratorLocalInductionBoundaryUp} :
    generatorLocalInductionBoundaryToEventFlow x =
      generatorLocalInductionBoundaryToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      generatorLocalInductionBoundaryFromEventFlow
          (generatorLocalInductionBoundaryToEventFlow x) =
        generatorLocalInductionBoundaryFromEventFlow
          (generatorLocalInductionBoundaryToEventFlow y) :=
    congrArg generatorLocalInductionBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (generatorLocalInductionBoundary_round_trip x).symm
      (Eq.trans hread (generatorLocalInductionBoundary_round_trip y)))

instance generatorLocalInductionBoundaryBHistCarrier :
    BHistCarrier GeneratorLocalInductionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := generatorLocalInductionBoundaryToEventFlow
  fromEventFlow := generatorLocalInductionBoundaryFromEventFlow

private def generatorLocalInductionBoundaryChapterTasteGateConcrete :
    @ChapterTasteGate GeneratorLocalInductionBoundaryUp
      generatorLocalInductionBoundaryBHistCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      generatorLocalInductionBoundaryFromEventFlow
        (generatorLocalInductionBoundaryToEventFlow x) = some x
    exact generatorLocalInductionBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (generatorLocalInductionBoundaryToEventFlow_injective heq)

instance generatorLocalInductionBoundaryChapterTasteGate :
    ChapterTasteGate GeneratorLocalInductionBoundaryUp :=
  generatorLocalInductionBoundaryChapterTasteGateConcrete

def generatorLocalInductionBoundaryFields :
    GeneratorLocalInductionBoundaryUp -> List BHist
  | GeneratorLocalInductionBoundaryUp.mk generatorDomain eliminatorLocality inductionLedger
      freeFloatingRefusal transport continuation provenance name =>
      [generatorDomain, eliminatorLocality, inductionLedger, freeFloatingRefusal, transport,
        continuation, provenance, name]

private theorem generatorLocalInductionBoundary_field_faithful :
    forall x y : GeneratorLocalInductionBoundaryUp,
      generatorLocalInductionBoundaryFields x =
        generatorLocalInductionBoundaryFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk generatorDomain1 eliminatorLocality1 inductionLedger1 freeFloatingRefusal1
      transport1 continuation1 provenance1 name1 =>
      cases y with
      | mk generatorDomain2 eliminatorLocality2 inductionLedger2 freeFloatingRefusal2
          transport2 continuation2 provenance2 name2 =>
          cases h
          rfl

private def generatorLocalInductionBoundaryFieldFaithfulConcrete :
    @FieldFaithful GeneratorLocalInductionBoundaryUp
      generatorLocalInductionBoundaryBHistCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  fields := generatorLocalInductionBoundaryFields
  field_faithful := generatorLocalInductionBoundary_field_faithful

instance generatorLocalInductionBoundaryFieldFaithful :
    FieldFaithful GeneratorLocalInductionBoundaryUp :=
  generatorLocalInductionBoundaryFieldFaithfulConcrete

private def generatorLocalInductionBoundaryWitnessPair :
    Σ' (x : GeneratorLocalInductionBoundaryUp) (y : GeneratorLocalInductionBoundaryUp),
      x ≠ y :=
  ⟨GeneratorLocalInductionBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
    GeneratorLocalInductionBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
    by
      intro h
      cases h⟩

private def generatorLocalInductionBoundaryNontrivialConcrete :
    Nontrivial GeneratorLocalInductionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair := generatorLocalInductionBoundaryWitnessPair

instance generatorLocalInductionBoundaryNontrivial :
    Nontrivial GeneratorLocalInductionBoundaryUp :=
  generatorLocalInductionBoundaryNontrivialConcrete

def taste_gate : ChapterTasteGate GeneratorLocalInductionBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  generatorLocalInductionBoundaryChapterTasteGateConcrete

theorem GeneratorLocalInductionBoundaryTasteGate_single_carrier_alignment :
    (forall h : BHist,
      generatorLocalInductionBoundaryDecodeBHist
        (generatorLocalInductionBoundaryEncodeBHist h) = h) /\
      (forall x : GeneratorLocalInductionBoundaryUp,
        generatorLocalInductionBoundaryFromEventFlow
          (generatorLocalInductionBoundaryToEventFlow x) = some x) /\
        (forall x y : GeneratorLocalInductionBoundaryUp,
          generatorLocalInductionBoundaryToEventFlow x =
            generatorLocalInductionBoundaryToEventFlow y -> x = y) /\
          (forall x y : GeneratorLocalInductionBoundaryUp,
            generatorLocalInductionBoundaryFields x =
              generatorLocalInductionBoundaryFields y -> x = y) /\
            Nonempty (Σ' (x : GeneratorLocalInductionBoundaryUp)
              (y : GeneratorLocalInductionBoundaryUp), x ≠ y) /\
              generatorLocalInductionBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact generatorLocalInductionBoundaryDecode_encode_bhist
  · constructor
    · exact generatorLocalInductionBoundary_round_trip
    · constructor
      · intro x y heq
        exact generatorLocalInductionBoundaryToEventFlow_injective heq
      · constructor
        · exact generatorLocalInductionBoundary_field_faithful
        · constructor
          · exact
              ⟨GeneratorLocalInductionBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                GeneratorLocalInductionBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩
          · rfl

end BEDC.Derived.GeneratorLocalInductionBoundaryUp.TasteGate

namespace BEDC.Derived.GeneratorLocalInductionBoundaryUp

def taste_gate :
    BEDC.Meta.TasteGate.ChapterTasteGate
      TasteGate.GeneratorLocalInductionBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  TasteGate.taste_gate

end BEDC.Derived.GeneratorLocalInductionBoundaryUp
