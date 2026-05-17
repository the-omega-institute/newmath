import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UnaryContinuationCategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UnaryContinuationCategoryUp : Type where
  | mk :
      (objects hom identity composition transport provenance localName : BHist) →
      UnaryContinuationCategoryUp
  deriving DecidableEq

def unaryContinuationCategoryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: unaryContinuationCategoryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: unaryContinuationCategoryEncodeBHist h

def unaryContinuationCategoryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (unaryContinuationCategoryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (unaryContinuationCategoryDecodeBHist tail)

private theorem unaryContinuationCategory_decode_encode_bhist :
    ∀ h : BHist,
      unaryContinuationCategoryDecodeBHist (unaryContinuationCategoryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def unaryContinuationCategoryFields :
    UnaryContinuationCategoryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UnaryContinuationCategoryUp.mk objects hom identity composition transport provenance
      localName =>
      [objects, hom, identity, composition, transport, provenance, localName]

def unaryContinuationCategoryToEventFlow :
    UnaryContinuationCategoryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UnaryContinuationCategoryUp.mk objects hom identity composition transport provenance
      localName =>
      [[BMark.b0],
        unaryContinuationCategoryEncodeBHist objects,
        [BMark.b1, BMark.b0],
        unaryContinuationCategoryEncodeBHist hom,
        [BMark.b1, BMark.b1, BMark.b0],
        unaryContinuationCategoryEncodeBHist identity,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        unaryContinuationCategoryEncodeBHist composition,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        unaryContinuationCategoryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        unaryContinuationCategoryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        unaryContinuationCategoryEncodeBHist localName]

def unaryContinuationCategoryFromEventFlow :
    EventFlow → Option UnaryContinuationCategoryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | objects :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | hom :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | identity :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | composition :: rest7 =>
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
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | localName :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (UnaryContinuationCategoryUp.mk
                                                                  (unaryContinuationCategoryDecodeBHist
                                                                    objects)
                                                                  (unaryContinuationCategoryDecodeBHist
                                                                    hom)
                                                                  (unaryContinuationCategoryDecodeBHist
                                                                    identity)
                                                                  (unaryContinuationCategoryDecodeBHist
                                                                    composition)
                                                                  (unaryContinuationCategoryDecodeBHist
                                                                    transport)
                                                                  (unaryContinuationCategoryDecodeBHist
                                                                    provenance)
                                                                  (unaryContinuationCategoryDecodeBHist
                                                                    localName))
                                                          | _ :: _ => none

private theorem unaryContinuationCategory_round_trip :
    ∀ x : UnaryContinuationCategoryUp,
      unaryContinuationCategoryFromEventFlow
        (unaryContinuationCategoryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk objects hom identity composition transport provenance localName =>
      change
        some
          (UnaryContinuationCategoryUp.mk
            (unaryContinuationCategoryDecodeBHist
              (unaryContinuationCategoryEncodeBHist objects))
            (unaryContinuationCategoryDecodeBHist
              (unaryContinuationCategoryEncodeBHist hom))
            (unaryContinuationCategoryDecodeBHist
              (unaryContinuationCategoryEncodeBHist identity))
            (unaryContinuationCategoryDecodeBHist
              (unaryContinuationCategoryEncodeBHist composition))
            (unaryContinuationCategoryDecodeBHist
              (unaryContinuationCategoryEncodeBHist transport))
            (unaryContinuationCategoryDecodeBHist
              (unaryContinuationCategoryEncodeBHist provenance))
            (unaryContinuationCategoryDecodeBHist
              (unaryContinuationCategoryEncodeBHist localName))) =
          some
            (UnaryContinuationCategoryUp.mk objects hom identity composition transport
              provenance localName)
      rw [unaryContinuationCategory_decode_encode_bhist objects,
        unaryContinuationCategory_decode_encode_bhist hom,
        unaryContinuationCategory_decode_encode_bhist identity,
        unaryContinuationCategory_decode_encode_bhist composition,
        unaryContinuationCategory_decode_encode_bhist transport,
        unaryContinuationCategory_decode_encode_bhist provenance,
        unaryContinuationCategory_decode_encode_bhist localName]

private theorem unaryContinuationCategoryToEventFlow_injective
    {x y : UnaryContinuationCategoryUp} :
    unaryContinuationCategoryToEventFlow x =
      unaryContinuationCategoryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      unaryContinuationCategoryFromEventFlow (unaryContinuationCategoryToEventFlow x) =
        unaryContinuationCategoryFromEventFlow (unaryContinuationCategoryToEventFlow y) :=
    congrArg unaryContinuationCategoryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (unaryContinuationCategory_round_trip x).symm
      (Eq.trans hread (unaryContinuationCategory_round_trip y)))

private theorem unaryContinuationCategory_field_faithful :
    ∀ x y : UnaryContinuationCategoryUp,
      unaryContinuationCategoryFields x = unaryContinuationCategoryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk objects hom identity composition transport provenance localName =>
      cases y with
      | mk objects' hom' identity' composition' transport' provenance' localName' =>
          cases hfields
          rfl

instance unaryContinuationCategoryBHistCarrier :
    BHistCarrier UnaryContinuationCategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := unaryContinuationCategoryToEventFlow
  fromEventFlow := unaryContinuationCategoryFromEventFlow

instance unaryContinuationCategoryChapterTasteGate :
    ChapterTasteGate UnaryContinuationCategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      unaryContinuationCategoryFromEventFlow
        (unaryContinuationCategoryToEventFlow x) = some x
    exact unaryContinuationCategory_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (unaryContinuationCategoryToEventFlow_injective heq)

instance unaryContinuationCategoryFieldFaithful :
    FieldFaithful UnaryContinuationCategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := unaryContinuationCategoryFields
  field_faithful := unaryContinuationCategory_field_faithful

instance unaryContinuationCategoryNontrivial :
    Nontrivial UnaryContinuationCategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UnaryContinuationCategoryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      UnaryContinuationCategoryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UnaryContinuationCategoryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  unaryContinuationCategoryChapterTasteGate

theorem UnaryContinuationCategoryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      unaryContinuationCategoryDecodeBHist (unaryContinuationCategoryEncodeBHist h) = h) ∧
      (∀ x : UnaryContinuationCategoryUp,
        unaryContinuationCategoryFromEventFlow
          (unaryContinuationCategoryToEventFlow x) = some x) ∧
        (∀ x y : UnaryContinuationCategoryUp,
          unaryContinuationCategoryToEventFlow x =
            unaryContinuationCategoryToEventFlow y → x = y) ∧
          unaryContinuationCategoryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact unaryContinuationCategory_decode_encode_bhist
  · constructor
    · exact unaryContinuationCategory_round_trip
    · constructor
      · intro x y heq
        exact unaryContinuationCategoryToEventFlow_injective heq
      · rfl

end BEDC.Derived.UnaryContinuationCategoryUp
