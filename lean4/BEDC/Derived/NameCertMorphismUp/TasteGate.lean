import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NameCertMorphismUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NameCertMorphismUp : Type where
  | mk :
      (sourceCert targetCert graph samePreservation route provenance localName : BHist) →
        NameCertMorphismUp
  deriving DecidableEq

def nameCertMorphismEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nameCertMorphismEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nameCertMorphismEncodeBHist h

def nameCertMorphismDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nameCertMorphismDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nameCertMorphismDecodeBHist tail)

private theorem nameCertMorphismDecode_encode_bhist :
    ∀ h : BHist, nameCertMorphismDecodeBHist (nameCertMorphismEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def nameCertMorphismToEventFlow : NameCertMorphismUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NameCertMorphismUp.mk sourceCert targetCert graph samePreservation route provenance
      localName =>
      [[BMark.b0],
        nameCertMorphismEncodeBHist sourceCert,
        [BMark.b1, BMark.b0],
        nameCertMorphismEncodeBHist targetCert,
        [BMark.b1, BMark.b1, BMark.b0],
        nameCertMorphismEncodeBHist graph,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nameCertMorphismEncodeBHist samePreservation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nameCertMorphismEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nameCertMorphismEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nameCertMorphismEncodeBHist localName]

def nameCertMorphismFromEventFlow : EventFlow → Option NameCertMorphismUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | sourceCert :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | targetCert :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | graph :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | samePreservation :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | route :: rest9 =>
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
                                                                (NameCertMorphismUp.mk
                                                                  (nameCertMorphismDecodeBHist
                                                                    sourceCert)
                                                                  (nameCertMorphismDecodeBHist
                                                                    targetCert)
                                                                  (nameCertMorphismDecodeBHist
                                                                    graph)
                                                                  (nameCertMorphismDecodeBHist
                                                                    samePreservation)
                                                                  (nameCertMorphismDecodeBHist
                                                                    route)
                                                                  (nameCertMorphismDecodeBHist
                                                                    provenance)
                                                                  (nameCertMorphismDecodeBHist
                                                                    localName))
                                                          | _ :: _ => none

private theorem nameCertMorphism_round_trip :
    ∀ x : NameCertMorphismUp,
      nameCertMorphismFromEventFlow (nameCertMorphismToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceCert targetCert graph samePreservation route provenance localName =>
      change
        some
          (NameCertMorphismUp.mk
            (nameCertMorphismDecodeBHist (nameCertMorphismEncodeBHist sourceCert))
            (nameCertMorphismDecodeBHist (nameCertMorphismEncodeBHist targetCert))
            (nameCertMorphismDecodeBHist (nameCertMorphismEncodeBHist graph))
            (nameCertMorphismDecodeBHist (nameCertMorphismEncodeBHist samePreservation))
            (nameCertMorphismDecodeBHist (nameCertMorphismEncodeBHist route))
            (nameCertMorphismDecodeBHist (nameCertMorphismEncodeBHist provenance))
            (nameCertMorphismDecodeBHist (nameCertMorphismEncodeBHist localName))) =
          some
            (NameCertMorphismUp.mk sourceCert targetCert graph samePreservation route provenance
              localName)
      rw [nameCertMorphismDecode_encode_bhist sourceCert,
        nameCertMorphismDecode_encode_bhist targetCert,
        nameCertMorphismDecode_encode_bhist graph,
        nameCertMorphismDecode_encode_bhist samePreservation,
        nameCertMorphismDecode_encode_bhist route,
        nameCertMorphismDecode_encode_bhist provenance,
        nameCertMorphismDecode_encode_bhist localName]

private theorem nameCertMorphismToEventFlow_injective {x y : NameCertMorphismUp} :
    nameCertMorphismToEventFlow x = nameCertMorphismToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nameCertMorphismFromEventFlow (nameCertMorphismToEventFlow x) =
        nameCertMorphismFromEventFlow (nameCertMorphismToEventFlow y) :=
    congrArg nameCertMorphismFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (nameCertMorphism_round_trip x).symm
      (Eq.trans hread (nameCertMorphism_round_trip y)))

instance nameCertMorphismBHistCarrier : BHistCarrier NameCertMorphismUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nameCertMorphismToEventFlow
  fromEventFlow := nameCertMorphismFromEventFlow

instance nameCertMorphismChapterTasteGate : ChapterTasteGate NameCertMorphismUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change nameCertMorphismFromEventFlow (nameCertMorphismToEventFlow x) = some x
    exact nameCertMorphism_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (nameCertMorphismToEventFlow_injective heq)

def taste_gate : ChapterTasteGate NameCertMorphismUp :=
  nameCertMorphismChapterTasteGate

theorem NameCertMorphismTasteGate_single_carrier_alignment :
    (∀ h : BHist, nameCertMorphismDecodeBHist (nameCertMorphismEncodeBHist h) = h) ∧
      (∀ x : NameCertMorphismUp,
        nameCertMorphismFromEventFlow (nameCertMorphismToEventFlow x) = some x) ∧
        (∀ x y : NameCertMorphismUp,
          nameCertMorphismToEventFlow x = nameCertMorphismToEventFlow y → x = y) ∧
          nameCertMorphismEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact nameCertMorphismDecode_encode_bhist
  · constructor
    · exact nameCertMorphism_round_trip
    · constructor
      · intro x y heq
        exact nameCertMorphismToEventFlow_injective heq
      · rfl

end BEDC.Derived.NameCertMorphismUp
