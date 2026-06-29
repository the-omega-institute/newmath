import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HypercoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HypercoverUp : Type where
  | mk
      (site levelwiseCover matchingObject cech sheafification descent
        transport replay provenance localName : BHist) :
      HypercoverUp
  deriving DecidableEq

def hypercoverEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hypercoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hypercoverEncodeBHist h

def hypercoverDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hypercoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hypercoverDecodeBHist tail)

private theorem hypercoverDecode_encode_bhist :
    ∀ h : BHist, hypercoverDecodeBHist (hypercoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def hypercoverToEventFlow : HypercoverUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HypercoverUp.mk site levelwiseCover matchingObject cech sheafification descent
      transport replay provenance localName =>
      [[BMark.b0],
        hypercoverEncodeBHist site,
        [BMark.b1, BMark.b0],
        hypercoverEncodeBHist levelwiseCover,
        [BMark.b1, BMark.b1, BMark.b0],
        hypercoverEncodeBHist matchingObject,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hypercoverEncodeBHist cech,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hypercoverEncodeBHist sheafification,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hypercoverEncodeBHist descent,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hypercoverEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        hypercoverEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        hypercoverEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        hypercoverEncodeBHist localName]

def hypercoverFromEventFlow : EventFlow → Option HypercoverUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | site :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | levelwiseCover :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | matchingObject :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | cech :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | sheafification :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | descent :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | replay :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | localName :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (HypercoverUp.mk
                                                                                          (hypercoverDecodeBHist site)
                                                                                          (hypercoverDecodeBHist levelwiseCover)
                                                                                          (hypercoverDecodeBHist matchingObject)
                                                                                          (hypercoverDecodeBHist cech)
                                                                                          (hypercoverDecodeBHist sheafification)
                                                                                          (hypercoverDecodeBHist descent)
                                                                                          (hypercoverDecodeBHist transport)
                                                                                          (hypercoverDecodeBHist replay)
                                                                                          (hypercoverDecodeBHist provenance)
                                                                                          (hypercoverDecodeBHist localName))
                                                                                  | _ :: _ => none

private theorem hypercover_round_trip :
    ∀ x : HypercoverUp, hypercoverFromEventFlow (hypercoverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk site levelwiseCover matchingObject cech sheafification descent
      transport replay provenance localName =>
      change
        some
          (HypercoverUp.mk
            (hypercoverDecodeBHist (hypercoverEncodeBHist site))
            (hypercoverDecodeBHist (hypercoverEncodeBHist levelwiseCover))
            (hypercoverDecodeBHist (hypercoverEncodeBHist matchingObject))
            (hypercoverDecodeBHist (hypercoverEncodeBHist cech))
            (hypercoverDecodeBHist (hypercoverEncodeBHist sheafification))
            (hypercoverDecodeBHist (hypercoverEncodeBHist descent))
            (hypercoverDecodeBHist (hypercoverEncodeBHist transport))
            (hypercoverDecodeBHist (hypercoverEncodeBHist replay))
            (hypercoverDecodeBHist (hypercoverEncodeBHist provenance))
            (hypercoverDecodeBHist (hypercoverEncodeBHist localName))) =
          some
            (HypercoverUp.mk site levelwiseCover matchingObject cech sheafification descent
              transport replay provenance localName)
      rw [hypercoverDecode_encode_bhist site,
        hypercoverDecode_encode_bhist levelwiseCover,
        hypercoverDecode_encode_bhist matchingObject,
        hypercoverDecode_encode_bhist cech,
        hypercoverDecode_encode_bhist sheafification,
        hypercoverDecode_encode_bhist descent,
        hypercoverDecode_encode_bhist transport,
        hypercoverDecode_encode_bhist replay,
        hypercoverDecode_encode_bhist provenance,
        hypercoverDecode_encode_bhist localName]

private theorem hypercoverToEventFlow_injective {x y : HypercoverUp} :
    hypercoverToEventFlow x = hypercoverToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hypercoverFromEventFlow (hypercoverToEventFlow x) =
        hypercoverFromEventFlow (hypercoverToEventFlow y) :=
    congrArg hypercoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hypercover_round_trip x).symm
      (Eq.trans hread (hypercover_round_trip y)))

instance hypercoverBHistCarrier : BHistCarrier HypercoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hypercoverToEventFlow
  fromEventFlow := hypercoverFromEventFlow

instance hypercoverChapterTasteGate : ChapterTasteGate HypercoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hypercoverFromEventFlow (hypercoverToEventFlow x) = some x
    exact hypercover_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hypercoverToEventFlow_injective heq)

theorem HypercoverTasteGate_single_carrier_alignment :
    (∀ h : BHist, hypercoverDecodeBHist (hypercoverEncodeBHist h) = h) ∧
      (∀ x : HypercoverUp,
        hypercoverFromEventFlow (hypercoverToEventFlow x) = some x) ∧
        (∀ x y : HypercoverUp,
          hypercoverToEventFlow x = hypercoverToEventFlow y → x = y) ∧
          hypercoverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact hypercoverDecode_encode_bhist
  · constructor
    · exact hypercover_round_trip
    · constructor
      · intro x y heq
        exact hypercoverToEventFlow_injective heq
      · rfl

end BEDC.Derived.HypercoverUp
