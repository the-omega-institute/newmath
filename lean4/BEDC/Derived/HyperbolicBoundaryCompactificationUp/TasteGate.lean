import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperbolicBoundaryCompactificationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperbolicBoundaryCompactificationUp : Type where
  | mk
      (metric visualBoundary gromovBoundary visualMetric busemannBoundary boundaryShadow realSeal
        transport replay provenance nameCert : BHist) :
      HyperbolicBoundaryCompactificationUp
  deriving DecidableEq

def hyperbolicBoundaryCompactificationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperbolicBoundaryCompactificationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperbolicBoundaryCompactificationEncodeBHist h

def hyperbolicBoundaryCompactificationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperbolicBoundaryCompactificationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperbolicBoundaryCompactificationDecodeBHist tail)

private theorem hyperbolicBoundaryCompactification_decode_encode_bhist :
    ∀ h : BHist,
      hyperbolicBoundaryCompactificationDecodeBHist
        (hyperbolicBoundaryCompactificationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def hyperbolicBoundaryCompactificationToEventFlow :
    HyperbolicBoundaryCompactificationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HyperbolicBoundaryCompactificationUp.mk metric visualBoundary gromovBoundary visualMetric
      busemannBoundary boundaryShadow realSeal transport replay provenance nameCert =>
      [[BMark.b0],
        hyperbolicBoundaryCompactificationEncodeBHist metric,
        [BMark.b1, BMark.b0],
        hyperbolicBoundaryCompactificationEncodeBHist visualBoundary,
        [BMark.b1, BMark.b1, BMark.b0],
        hyperbolicBoundaryCompactificationEncodeBHist gromovBoundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hyperbolicBoundaryCompactificationEncodeBHist visualMetric,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hyperbolicBoundaryCompactificationEncodeBHist busemannBoundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hyperbolicBoundaryCompactificationEncodeBHist boundaryShadow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hyperbolicBoundaryCompactificationEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        hyperbolicBoundaryCompactificationEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        hyperbolicBoundaryCompactificationEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        hyperbolicBoundaryCompactificationEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hyperbolicBoundaryCompactificationEncodeBHist nameCert]

def hyperbolicBoundaryCompactificationFromEventFlow :
    EventFlow → Option HyperbolicBoundaryCompactificationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | metric :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | visualBoundary :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | gromovBoundary :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | visualMetric :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | busemannBoundary :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | boundaryShadow :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | realSeal :: rest13 =>
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
                                                                      | replay :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | provenance ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match
                                                                                        rest20
                                                                                      with
                                                                                      | [] =>
                                                                                          none
                                                                                      | nameCert ::
                                                                                          rest21 =>
                                                                                          match
                                                                                            rest21
                                                                                          with
                                                                                          | [] =>
                                                                                              some
                                                                                                (HyperbolicBoundaryCompactificationUp.mk
                                                                                                  (hyperbolicBoundaryCompactificationDecodeBHist
                                                                                                    metric)
                                                                                                  (hyperbolicBoundaryCompactificationDecodeBHist
                                                                                                    visualBoundary)
                                                                                                  (hyperbolicBoundaryCompactificationDecodeBHist
                                                                                                    gromovBoundary)
                                                                                                  (hyperbolicBoundaryCompactificationDecodeBHist
                                                                                                    visualMetric)
                                                                                                  (hyperbolicBoundaryCompactificationDecodeBHist
                                                                                                    busemannBoundary)
                                                                                                  (hyperbolicBoundaryCompactificationDecodeBHist
                                                                                                    boundaryShadow)
                                                                                                  (hyperbolicBoundaryCompactificationDecodeBHist
                                                                                                    realSeal)
                                                                                                  (hyperbolicBoundaryCompactificationDecodeBHist
                                                                                                    transport)
                                                                                                  (hyperbolicBoundaryCompactificationDecodeBHist
                                                                                                    replay)
                                                                                                  (hyperbolicBoundaryCompactificationDecodeBHist
                                                                                                    provenance)
                                                                                                  (hyperbolicBoundaryCompactificationDecodeBHist
                                                                                                    nameCert))
                                                                                          | _ :: _ =>
                                                                                              none

private theorem hyperbolicBoundaryCompactification_round_trip :
    ∀ x : HyperbolicBoundaryCompactificationUp,
      hyperbolicBoundaryCompactificationFromEventFlow
        (hyperbolicBoundaryCompactificationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metric visualBoundary gromovBoundary visualMetric busemannBoundary boundaryShadow
      realSeal transport replay provenance nameCert =>
      change
        some
          (HyperbolicBoundaryCompactificationUp.mk
            (hyperbolicBoundaryCompactificationDecodeBHist
              (hyperbolicBoundaryCompactificationEncodeBHist metric))
            (hyperbolicBoundaryCompactificationDecodeBHist
              (hyperbolicBoundaryCompactificationEncodeBHist visualBoundary))
            (hyperbolicBoundaryCompactificationDecodeBHist
              (hyperbolicBoundaryCompactificationEncodeBHist gromovBoundary))
            (hyperbolicBoundaryCompactificationDecodeBHist
              (hyperbolicBoundaryCompactificationEncodeBHist visualMetric))
            (hyperbolicBoundaryCompactificationDecodeBHist
              (hyperbolicBoundaryCompactificationEncodeBHist busemannBoundary))
            (hyperbolicBoundaryCompactificationDecodeBHist
              (hyperbolicBoundaryCompactificationEncodeBHist boundaryShadow))
            (hyperbolicBoundaryCompactificationDecodeBHist
              (hyperbolicBoundaryCompactificationEncodeBHist realSeal))
            (hyperbolicBoundaryCompactificationDecodeBHist
              (hyperbolicBoundaryCompactificationEncodeBHist transport))
            (hyperbolicBoundaryCompactificationDecodeBHist
              (hyperbolicBoundaryCompactificationEncodeBHist replay))
            (hyperbolicBoundaryCompactificationDecodeBHist
              (hyperbolicBoundaryCompactificationEncodeBHist provenance))
            (hyperbolicBoundaryCompactificationDecodeBHist
              (hyperbolicBoundaryCompactificationEncodeBHist nameCert))) =
          some
            (HyperbolicBoundaryCompactificationUp.mk metric visualBoundary gromovBoundary
              visualMetric busemannBoundary boundaryShadow realSeal transport replay provenance
              nameCert)
      rw [hyperbolicBoundaryCompactification_decode_encode_bhist metric,
        hyperbolicBoundaryCompactification_decode_encode_bhist visualBoundary,
        hyperbolicBoundaryCompactification_decode_encode_bhist gromovBoundary,
        hyperbolicBoundaryCompactification_decode_encode_bhist visualMetric,
        hyperbolicBoundaryCompactification_decode_encode_bhist busemannBoundary,
        hyperbolicBoundaryCompactification_decode_encode_bhist boundaryShadow,
        hyperbolicBoundaryCompactification_decode_encode_bhist realSeal,
        hyperbolicBoundaryCompactification_decode_encode_bhist transport,
        hyperbolicBoundaryCompactification_decode_encode_bhist replay,
        hyperbolicBoundaryCompactification_decode_encode_bhist provenance,
        hyperbolicBoundaryCompactification_decode_encode_bhist nameCert]

private theorem hyperbolicBoundaryCompactificationToEventFlow_injective
    {x y : HyperbolicBoundaryCompactificationUp} :
    hyperbolicBoundaryCompactificationToEventFlow x =
      hyperbolicBoundaryCompactificationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hyperbolicBoundaryCompactificationFromEventFlow
          (hyperbolicBoundaryCompactificationToEventFlow x) =
        hyperbolicBoundaryCompactificationFromEventFlow
          (hyperbolicBoundaryCompactificationToEventFlow y) :=
    congrArg hyperbolicBoundaryCompactificationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hyperbolicBoundaryCompactification_round_trip x).symm
      (Eq.trans hread (hyperbolicBoundaryCompactification_round_trip y)))

instance hyperbolicBoundaryCompactificationBHistCarrier :
    BHistCarrier HyperbolicBoundaryCompactificationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperbolicBoundaryCompactificationToEventFlow
  fromEventFlow := hyperbolicBoundaryCompactificationFromEventFlow

instance hyperbolicBoundaryCompactificationChapterTasteGate :
    ChapterTasteGate HyperbolicBoundaryCompactificationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hyperbolicBoundaryCompactificationFromEventFlow
        (hyperbolicBoundaryCompactificationToEventFlow x) = some x
    exact hyperbolicBoundaryCompactification_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hyperbolicBoundaryCompactificationToEventFlow_injective heq)

def taste_gate : ChapterTasteGate HyperbolicBoundaryCompactificationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hyperbolicBoundaryCompactificationChapterTasteGate

theorem HyperbolicBoundaryCompactificationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      hyperbolicBoundaryCompactificationDecodeBHist
        (hyperbolicBoundaryCompactificationEncodeBHist h) = h) ∧
      (∀ x : HyperbolicBoundaryCompactificationUp,
        hyperbolicBoundaryCompactificationFromEventFlow
          (hyperbolicBoundaryCompactificationToEventFlow x) = some x) ∧
        (∀ x y : HyperbolicBoundaryCompactificationUp,
          hyperbolicBoundaryCompactificationToEventFlow x =
            hyperbolicBoundaryCompactificationToEventFlow y → x = y) ∧
          hyperbolicBoundaryCompactificationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact hyperbolicBoundaryCompactification_decode_encode_bhist
  · constructor
    · exact hyperbolicBoundaryCompactification_round_trip
    · constructor
      · intro x y heq
        exact hyperbolicBoundaryCompactificationToEventFlow_injective heq
      · rfl

end BEDC.Derived.HyperbolicBoundaryCompactificationUp
