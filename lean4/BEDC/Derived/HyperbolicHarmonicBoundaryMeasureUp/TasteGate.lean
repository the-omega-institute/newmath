import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperbolicHarmonicBoundaryMeasureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperbolicHarmonicBoundaryMeasureUp : Type where
  | mk (D B V K R W H C P N : BHist) : HyperbolicHarmonicBoundaryMeasureUp
  deriving DecidableEq

def hyperbolicHarmonicBoundaryMeasureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperbolicHarmonicBoundaryMeasureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperbolicHarmonicBoundaryMeasureEncodeBHist h

def hyperbolicHarmonicBoundaryMeasureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperbolicHarmonicBoundaryMeasureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperbolicHarmonicBoundaryMeasureDecodeBHist tail)

private theorem hyperbolicHarmonicBoundaryMeasureDecode_encode_bhist :
    ∀ h : BHist,
      hyperbolicHarmonicBoundaryMeasureDecodeBHist
        (hyperbolicHarmonicBoundaryMeasureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def hyperbolicHarmonicBoundaryMeasureToEventFlow :
    HyperbolicHarmonicBoundaryMeasureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HyperbolicHarmonicBoundaryMeasureUp.mk D B V K R W H C P N =>
      [[BMark.b0],
        hyperbolicHarmonicBoundaryMeasureEncodeBHist D,
        [BMark.b1, BMark.b0],
        hyperbolicHarmonicBoundaryMeasureEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b0],
        hyperbolicHarmonicBoundaryMeasureEncodeBHist V,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hyperbolicHarmonicBoundaryMeasureEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hyperbolicHarmonicBoundaryMeasureEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hyperbolicHarmonicBoundaryMeasureEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hyperbolicHarmonicBoundaryMeasureEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        hyperbolicHarmonicBoundaryMeasureEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        hyperbolicHarmonicBoundaryMeasureEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        hyperbolicHarmonicBoundaryMeasureEncodeBHist N]

def hyperbolicHarmonicBoundaryMeasureFromEventFlow :
    EventFlow → Option HyperbolicHarmonicBoundaryMeasureUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | D :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | B :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | V :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | K :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | R :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | W :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | H :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | C :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | P :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | N :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (HyperbolicHarmonicBoundaryMeasureUp.mk
                                                                                          (hyperbolicHarmonicBoundaryMeasureDecodeBHist D)
                                                                                          (hyperbolicHarmonicBoundaryMeasureDecodeBHist B)
                                                                                          (hyperbolicHarmonicBoundaryMeasureDecodeBHist V)
                                                                                          (hyperbolicHarmonicBoundaryMeasureDecodeBHist K)
                                                                                          (hyperbolicHarmonicBoundaryMeasureDecodeBHist R)
                                                                                          (hyperbolicHarmonicBoundaryMeasureDecodeBHist W)
                                                                                          (hyperbolicHarmonicBoundaryMeasureDecodeBHist H)
                                                                                          (hyperbolicHarmonicBoundaryMeasureDecodeBHist C)
                                                                                          (hyperbolicHarmonicBoundaryMeasureDecodeBHist P)
                                                                                          (hyperbolicHarmonicBoundaryMeasureDecodeBHist N))
                                                                                  | _ :: _ => none

private theorem hyperbolicHarmonicBoundaryMeasure_round_trip :
    ∀ x : HyperbolicHarmonicBoundaryMeasureUp,
      hyperbolicHarmonicBoundaryMeasureFromEventFlow
        (hyperbolicHarmonicBoundaryMeasureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D B V K R W H C P N =>
      change
        some
          (HyperbolicHarmonicBoundaryMeasureUp.mk
            (hyperbolicHarmonicBoundaryMeasureDecodeBHist
              (hyperbolicHarmonicBoundaryMeasureEncodeBHist D))
            (hyperbolicHarmonicBoundaryMeasureDecodeBHist
              (hyperbolicHarmonicBoundaryMeasureEncodeBHist B))
            (hyperbolicHarmonicBoundaryMeasureDecodeBHist
              (hyperbolicHarmonicBoundaryMeasureEncodeBHist V))
            (hyperbolicHarmonicBoundaryMeasureDecodeBHist
              (hyperbolicHarmonicBoundaryMeasureEncodeBHist K))
            (hyperbolicHarmonicBoundaryMeasureDecodeBHist
              (hyperbolicHarmonicBoundaryMeasureEncodeBHist R))
            (hyperbolicHarmonicBoundaryMeasureDecodeBHist
              (hyperbolicHarmonicBoundaryMeasureEncodeBHist W))
            (hyperbolicHarmonicBoundaryMeasureDecodeBHist
              (hyperbolicHarmonicBoundaryMeasureEncodeBHist H))
            (hyperbolicHarmonicBoundaryMeasureDecodeBHist
              (hyperbolicHarmonicBoundaryMeasureEncodeBHist C))
            (hyperbolicHarmonicBoundaryMeasureDecodeBHist
              (hyperbolicHarmonicBoundaryMeasureEncodeBHist P))
            (hyperbolicHarmonicBoundaryMeasureDecodeBHist
              (hyperbolicHarmonicBoundaryMeasureEncodeBHist N))) =
          some (HyperbolicHarmonicBoundaryMeasureUp.mk D B V K R W H C P N)
      rw [hyperbolicHarmonicBoundaryMeasureDecode_encode_bhist D,
        hyperbolicHarmonicBoundaryMeasureDecode_encode_bhist B,
        hyperbolicHarmonicBoundaryMeasureDecode_encode_bhist V,
        hyperbolicHarmonicBoundaryMeasureDecode_encode_bhist K,
        hyperbolicHarmonicBoundaryMeasureDecode_encode_bhist R,
        hyperbolicHarmonicBoundaryMeasureDecode_encode_bhist W,
        hyperbolicHarmonicBoundaryMeasureDecode_encode_bhist H,
        hyperbolicHarmonicBoundaryMeasureDecode_encode_bhist C,
        hyperbolicHarmonicBoundaryMeasureDecode_encode_bhist P,
        hyperbolicHarmonicBoundaryMeasureDecode_encode_bhist N]

private theorem hyperbolicHarmonicBoundaryMeasureToEventFlow_injective
    {x y : HyperbolicHarmonicBoundaryMeasureUp} :
    hyperbolicHarmonicBoundaryMeasureToEventFlow x =
      hyperbolicHarmonicBoundaryMeasureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hyperbolicHarmonicBoundaryMeasureFromEventFlow
          (hyperbolicHarmonicBoundaryMeasureToEventFlow x) =
        hyperbolicHarmonicBoundaryMeasureFromEventFlow
          (hyperbolicHarmonicBoundaryMeasureToEventFlow y) :=
    congrArg hyperbolicHarmonicBoundaryMeasureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hyperbolicHarmonicBoundaryMeasure_round_trip x).symm
      (Eq.trans hread (hyperbolicHarmonicBoundaryMeasure_round_trip y)))

def hyperbolicHarmonicBoundaryMeasureFields :
    HyperbolicHarmonicBoundaryMeasureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyperbolicHarmonicBoundaryMeasureUp.mk D B V K R W H C P N =>
      [D, B, V, K, R, W, H, C, P, N]

private theorem hyperbolicHarmonicBoundaryMeasure_field_faithful :
    ∀ x y : HyperbolicHarmonicBoundaryMeasureUp,
      hyperbolicHarmonicBoundaryMeasureFields x =
        hyperbolicHarmonicBoundaryMeasureFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 B1 V1 K1 R1 W1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 B2 V2 K2 R2 W2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance hyperbolicHarmonicBoundaryMeasureBHistCarrier :
    BHistCarrier HyperbolicHarmonicBoundaryMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperbolicHarmonicBoundaryMeasureToEventFlow
  fromEventFlow := hyperbolicHarmonicBoundaryMeasureFromEventFlow

instance taste_gate :
    ChapterTasteGate HyperbolicHarmonicBoundaryMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hyperbolicHarmonicBoundaryMeasureFromEventFlow
        (hyperbolicHarmonicBoundaryMeasureToEventFlow x) = some x
    exact hyperbolicHarmonicBoundaryMeasure_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hyperbolicHarmonicBoundaryMeasureToEventFlow_injective heq)

instance hyperbolicHarmonicBoundaryMeasureFieldFaithful :
    FieldFaithful HyperbolicHarmonicBoundaryMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hyperbolicHarmonicBoundaryMeasureFields
  field_faithful := hyperbolicHarmonicBoundaryMeasure_field_faithful

instance hyperbolicHarmonicBoundaryMeasureNontrivial :
    Nontrivial HyperbolicHarmonicBoundaryMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HyperbolicHarmonicBoundaryMeasureUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      HyperbolicHarmonicBoundaryMeasureUp.mk (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem HyperbolicHarmonicBoundaryMeasureTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      hyperbolicHarmonicBoundaryMeasureDecodeBHist
        (hyperbolicHarmonicBoundaryMeasureEncodeBHist h) = h) ∧
      (∀ x : HyperbolicHarmonicBoundaryMeasureUp,
        hyperbolicHarmonicBoundaryMeasureFromEventFlow
          (hyperbolicHarmonicBoundaryMeasureToEventFlow x) = some x) ∧
        (∀ x y : HyperbolicHarmonicBoundaryMeasureUp,
          hyperbolicHarmonicBoundaryMeasureToEventFlow x =
            hyperbolicHarmonicBoundaryMeasureToEventFlow y → x = y) ∧
          hyperbolicHarmonicBoundaryMeasureEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact hyperbolicHarmonicBoundaryMeasureDecode_encode_bhist
  · constructor
    · exact hyperbolicHarmonicBoundaryMeasure_round_trip
    · constructor
      · intro x y heq
        exact hyperbolicHarmonicBoundaryMeasureToEventFlow_injective heq
      · rfl

end BEDC.Derived.HyperbolicHarmonicBoundaryMeasureUp
