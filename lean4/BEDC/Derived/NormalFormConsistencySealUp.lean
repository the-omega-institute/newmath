import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NormalFormConsistencySealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NormalFormConsistencySealUp : Type where
  | mk :
      (typing falseRow normality theoremRow boundary transport routes provenance nameCert :
        BHist) →
        NormalFormConsistencySealUp
  deriving DecidableEq

def normalFormConsistencySealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: normalFormConsistencySealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: normalFormConsistencySealEncodeBHist h

def normalFormConsistencySealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (normalFormConsistencySealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (normalFormConsistencySealDecodeBHist tail)

private theorem normalFormConsistencySeal_decode_encode_bhist :
    ∀ h : BHist,
      normalFormConsistencySealDecodeBHist (normalFormConsistencySealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem normalFormConsistencySeal_mk_congr
    {typing typing' falseRow falseRow' normality normality' theoremRow theoremRow'
      boundary boundary' transport transport' routes routes' provenance provenance'
      nameCert nameCert' : BHist}
    (hTyping : typing' = typing)
    (hFalseRow : falseRow' = falseRow)
    (hNormality : normality' = normality)
    (hTheoremRow : theoremRow' = theoremRow)
    (hBoundary : boundary' = boundary)
    (hTransport : transport' = transport)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    NormalFormConsistencySealUp.mk typing' falseRow' normality' theoremRow' boundary'
        transport' routes' provenance' nameCert' =
      NormalFormConsistencySealUp.mk typing falseRow normality theoremRow boundary transport
        routes provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hTyping
  cases hFalseRow
  cases hNormality
  cases hTheoremRow
  cases hBoundary
  cases hTransport
  cases hRoutes
  cases hProvenance
  cases hNameCert
  rfl

def normalFormConsistencySealToEventFlow : NormalFormConsistencySealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NormalFormConsistencySealUp.mk typing falseRow normality theoremRow boundary transport
      routes provenance nameCert =>
      [[BMark.b0],
        normalFormConsistencySealEncodeBHist typing,
        [BMark.b1, BMark.b0],
        normalFormConsistencySealEncodeBHist falseRow,
        [BMark.b1, BMark.b1, BMark.b0],
        normalFormConsistencySealEncodeBHist normality,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        normalFormConsistencySealEncodeBHist theoremRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        normalFormConsistencySealEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        normalFormConsistencySealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        normalFormConsistencySealEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        normalFormConsistencySealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        normalFormConsistencySealEncodeBHist nameCert]

def normalFormConsistencySealFromEventFlow : EventFlow -> Option NormalFormConsistencySealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | typing :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | falseRow :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | normality :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | theoremRow :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | boundary :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | routes :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | nameCert :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (NormalFormConsistencySealUp.mk
                                                                                  (normalFormConsistencySealDecodeBHist
                                                                                    typing)
                                                                                  (normalFormConsistencySealDecodeBHist
                                                                                    falseRow)
                                                                                  (normalFormConsistencySealDecodeBHist
                                                                                    normality)
                                                                                  (normalFormConsistencySealDecodeBHist
                                                                                    theoremRow)
                                                                                  (normalFormConsistencySealDecodeBHist
                                                                                    boundary)
                                                                                  (normalFormConsistencySealDecodeBHist
                                                                                    transport)
                                                                                  (normalFormConsistencySealDecodeBHist
                                                                                    routes)
                                                                                  (normalFormConsistencySealDecodeBHist
                                                                                    provenance)
                                                                                  (normalFormConsistencySealDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ => none

private theorem normalFormConsistencySeal_round_trip :
    ∀ x : NormalFormConsistencySealUp,
      normalFormConsistencySealFromEventFlow
        (normalFormConsistencySealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk typing falseRow normality theoremRow boundary transport routes provenance nameCert =>
      change
        some
          (NormalFormConsistencySealUp.mk
            (normalFormConsistencySealDecodeBHist
              (normalFormConsistencySealEncodeBHist typing))
            (normalFormConsistencySealDecodeBHist
              (normalFormConsistencySealEncodeBHist falseRow))
            (normalFormConsistencySealDecodeBHist
              (normalFormConsistencySealEncodeBHist normality))
            (normalFormConsistencySealDecodeBHist
              (normalFormConsistencySealEncodeBHist theoremRow))
            (normalFormConsistencySealDecodeBHist
              (normalFormConsistencySealEncodeBHist boundary))
            (normalFormConsistencySealDecodeBHist
              (normalFormConsistencySealEncodeBHist transport))
            (normalFormConsistencySealDecodeBHist
              (normalFormConsistencySealEncodeBHist routes))
            (normalFormConsistencySealDecodeBHist
              (normalFormConsistencySealEncodeBHist provenance))
            (normalFormConsistencySealDecodeBHist
              (normalFormConsistencySealEncodeBHist nameCert))) =
          some
            (NormalFormConsistencySealUp.mk typing falseRow normality theoremRow boundary
              transport routes provenance nameCert)
      exact
        congrArg some
          (normalFormConsistencySeal_mk_congr
            (normalFormConsistencySeal_decode_encode_bhist typing)
            (normalFormConsistencySeal_decode_encode_bhist falseRow)
            (normalFormConsistencySeal_decode_encode_bhist normality)
            (normalFormConsistencySeal_decode_encode_bhist theoremRow)
            (normalFormConsistencySeal_decode_encode_bhist boundary)
            (normalFormConsistencySeal_decode_encode_bhist transport)
            (normalFormConsistencySeal_decode_encode_bhist routes)
            (normalFormConsistencySeal_decode_encode_bhist provenance)
            (normalFormConsistencySeal_decode_encode_bhist nameCert))

private theorem normalFormConsistencySealToEventFlow_injective
    {x y : NormalFormConsistencySealUp} :
    normalFormConsistencySealToEventFlow x = normalFormConsistencySealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      normalFormConsistencySealFromEventFlow (normalFormConsistencySealToEventFlow x) =
        normalFormConsistencySealFromEventFlow (normalFormConsistencySealToEventFlow y) :=
    congrArg normalFormConsistencySealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (normalFormConsistencySeal_round_trip x).symm
      (Eq.trans hread (normalFormConsistencySeal_round_trip y)))

instance normalFormConsistencySealBHistCarrier : BHistCarrier NormalFormConsistencySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := normalFormConsistencySealToEventFlow
  fromEventFlow := normalFormConsistencySealFromEventFlow

instance normalFormConsistencySealChapterTasteGate :
    ChapterTasteGate NormalFormConsistencySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      normalFormConsistencySealFromEventFlow
        (normalFormConsistencySealToEventFlow x) = some x
    exact normalFormConsistencySeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (normalFormConsistencySealToEventFlow_injective heq)

theorem NormalFormConsistencySealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      normalFormConsistencySealDecodeBHist (normalFormConsistencySealEncodeBHist h) = h) ∧
      (∀ x : NormalFormConsistencySealUp,
        normalFormConsistencySealFromEventFlow
          (normalFormConsistencySealToEventFlow x) = some x) ∧
        (∀ x y : NormalFormConsistencySealUp,
          normalFormConsistencySealToEventFlow x =
            normalFormConsistencySealToEventFlow y → x = y) ∧
          (∀ (x : NormalFormConsistencySealUp) w m,
            List.Mem w (normalFormConsistencySealToEventFlow x) →
              List.Mem m w → m = BMark.b0 ∨ m = BMark.b1) ∧
            normalFormConsistencySealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact normalFormConsistencySeal_decode_encode_bhist
  · constructor
    · exact normalFormConsistencySeal_round_trip
    · constructor
      · intro x y heq
        exact normalFormConsistencySealToEventFlow_injective heq
      · constructor
        · intro x w m hw hm
          exact BMark_generated_cases m
        · rfl

end BEDC.Derived.NormalFormConsistencySealUp
