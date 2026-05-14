import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- MetaCIC normalization frontier packet with the nine displayed BHist rows. -/
inductive MetaCICNormalizationFrontierUp : Type where
  | mk :
      (candidate closedCandidate finishedNormal endpoint obstruction transports routes
        provenance nameCert : BHist) →
      MetaCICNormalizationFrontierUp
  deriving DecidableEq

def metaCICNormalizationFrontierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICNormalizationFrontierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICNormalizationFrontierEncodeBHist h

def metaCICNormalizationFrontierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICNormalizationFrontierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICNormalizationFrontierDecodeBHist tail)

private theorem metaCICNormalizationFrontier_decode_encode_bhist :
    ∀ h : BHist,
      metaCICNormalizationFrontierDecodeBHist (metaCICNormalizationFrontierEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metaCICNormalizationFrontierFields :
    MetaCICNormalizationFrontierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICNormalizationFrontierUp.mk candidate closedCandidate finishedNormal endpoint
      obstruction transports routes provenance nameCert =>
      [candidate, closedCandidate, finishedNormal, endpoint, obstruction, transports, routes,
        provenance, nameCert]

def metaCICNormalizationFrontierToEventFlow :
    MetaCICNormalizationFrontierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metaCICNormalizationFrontierFields x).map metaCICNormalizationFrontierEncodeBHist

def metaCICNormalizationFrontierFromEventFlow :
    EventFlow → Option MetaCICNormalizationFrontierUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | candidate :: rest0 =>
      match rest0 with
      | [] => none
      | closedCandidate :: rest1 =>
          match rest1 with
          | [] => none
          | finishedNormal :: rest2 =>
              match rest2 with
              | [] => none
              | endpoint :: rest3 =>
                  match rest3 with
                  | [] => none
                  | obstruction :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transports :: rest5 =>
                          match rest5 with
                          | [] => none
                          | routes :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | nameCert :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (MetaCICNormalizationFrontierUp.mk
                                              (metaCICNormalizationFrontierDecodeBHist
                                                candidate)
                                              (metaCICNormalizationFrontierDecodeBHist
                                                closedCandidate)
                                              (metaCICNormalizationFrontierDecodeBHist
                                                finishedNormal)
                                              (metaCICNormalizationFrontierDecodeBHist endpoint)
                                              (metaCICNormalizationFrontierDecodeBHist
                                                obstruction)
                                              (metaCICNormalizationFrontierDecodeBHist
                                                transports)
                                              (metaCICNormalizationFrontierDecodeBHist routes)
                                              (metaCICNormalizationFrontierDecodeBHist
                                                provenance)
                                              (metaCICNormalizationFrontierDecodeBHist
                                                nameCert))
                                      | _ :: _ => none

private theorem metaCICNormalizationFrontier_round_trip :
    ∀ x : MetaCICNormalizationFrontierUp,
      metaCICNormalizationFrontierFromEventFlow
          (metaCICNormalizationFrontierToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk candidate closedCandidate finishedNormal endpoint obstruction transports routes
      provenance nameCert =>
      change
        some
          (MetaCICNormalizationFrontierUp.mk
            (metaCICNormalizationFrontierDecodeBHist
              (metaCICNormalizationFrontierEncodeBHist candidate))
            (metaCICNormalizationFrontierDecodeBHist
              (metaCICNormalizationFrontierEncodeBHist closedCandidate))
            (metaCICNormalizationFrontierDecodeBHist
              (metaCICNormalizationFrontierEncodeBHist finishedNormal))
            (metaCICNormalizationFrontierDecodeBHist
              (metaCICNormalizationFrontierEncodeBHist endpoint))
            (metaCICNormalizationFrontierDecodeBHist
              (metaCICNormalizationFrontierEncodeBHist obstruction))
            (metaCICNormalizationFrontierDecodeBHist
              (metaCICNormalizationFrontierEncodeBHist transports))
            (metaCICNormalizationFrontierDecodeBHist
              (metaCICNormalizationFrontierEncodeBHist routes))
            (metaCICNormalizationFrontierDecodeBHist
              (metaCICNormalizationFrontierEncodeBHist provenance))
            (metaCICNormalizationFrontierDecodeBHist
              (metaCICNormalizationFrontierEncodeBHist nameCert))) =
          some
            (MetaCICNormalizationFrontierUp.mk candidate closedCandidate finishedNormal
              endpoint obstruction transports routes provenance nameCert)
      rw [metaCICNormalizationFrontier_decode_encode_bhist candidate,
        metaCICNormalizationFrontier_decode_encode_bhist closedCandidate,
        metaCICNormalizationFrontier_decode_encode_bhist finishedNormal,
        metaCICNormalizationFrontier_decode_encode_bhist endpoint,
        metaCICNormalizationFrontier_decode_encode_bhist obstruction,
        metaCICNormalizationFrontier_decode_encode_bhist transports,
        metaCICNormalizationFrontier_decode_encode_bhist routes,
        metaCICNormalizationFrontier_decode_encode_bhist provenance,
        metaCICNormalizationFrontier_decode_encode_bhist nameCert]

private theorem metaCICNormalizationFrontierToEventFlow_injective
    {x y : MetaCICNormalizationFrontierUp} :
    metaCICNormalizationFrontierToEventFlow x =
        metaCICNormalizationFrontierToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICNormalizationFrontierFromEventFlow
          (metaCICNormalizationFrontierToEventFlow x) =
        metaCICNormalizationFrontierFromEventFlow
          (metaCICNormalizationFrontierToEventFlow y) :=
    congrArg metaCICNormalizationFrontierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICNormalizationFrontier_round_trip x).symm
      (Eq.trans hread (metaCICNormalizationFrontier_round_trip y)))

private theorem metaCICNormalizationFrontier_fields_faithful :
    ∀ x y : MetaCICNormalizationFrontierUp,
      metaCICNormalizationFrontierFields x = metaCICNormalizationFrontierFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk candidate₁ closedCandidate₁ finishedNormal₁ endpoint₁ obstruction₁ transports₁
      routes₁ provenance₁ nameCert₁ =>
      cases y with
      | mk candidate₂ closedCandidate₂ finishedNormal₂ endpoint₂ obstruction₂ transports₂
          routes₂ provenance₂ nameCert₂ =>
          injection hfields with hCandidate tail0
          injection tail0 with hClosedCandidate tail1
          injection tail1 with hFinishedNormal tail2
          injection tail2 with hEndpoint tail3
          injection tail3 with hObstruction tail4
          injection tail4 with hTransports tail5
          injection tail5 with hRoutes tail6
          injection tail6 with hProvenance tail7
          injection tail7 with hNameCert _
          subst hCandidate
          subst hClosedCandidate
          subst hFinishedNormal
          subst hEndpoint
          subst hObstruction
          subst hTransports
          subst hRoutes
          subst hProvenance
          subst hNameCert
          rfl

instance metaCICNormalizationFrontierBHistCarrier :
    BHistCarrier MetaCICNormalizationFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICNormalizationFrontierToEventFlow
  fromEventFlow := metaCICNormalizationFrontierFromEventFlow

instance metaCICNormalizationFrontierChapterTasteGate :
    ChapterTasteGate MetaCICNormalizationFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICNormalizationFrontierFromEventFlow
          (metaCICNormalizationFrontierToEventFlow x) =
        some x
    exact metaCICNormalizationFrontier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICNormalizationFrontierToEventFlow_injective heq)

instance metaCICNormalizationFrontierFieldFaithful :
    FieldFaithful MetaCICNormalizationFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICNormalizationFrontierFields
  field_faithful := metaCICNormalizationFrontier_fields_faithful

def taste_gate : ChapterTasteGate MetaCICNormalizationFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICNormalizationFrontierFromEventFlow
          (metaCICNormalizationFrontierToEventFlow x) =
        some x
    exact metaCICNormalizationFrontier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICNormalizationFrontierToEventFlow_injective heq)

theorem MetaCICNormalizationFrontierTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metaCICNormalizationFrontierDecodeBHist
          (metaCICNormalizationFrontierEncodeBHist h) =
        h) ∧
      (∀ x : MetaCICNormalizationFrontierUp,
        metaCICNormalizationFrontierFromEventFlow
            (metaCICNormalizationFrontierToEventFlow x) =
          some x) ∧
        (∀ x y : MetaCICNormalizationFrontierUp,
          metaCICNormalizationFrontierToEventFlow x =
              metaCICNormalizationFrontierToEventFlow y →
            x = y) ∧
          metaCICNormalizationFrontierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metaCICNormalizationFrontier_decode_encode_bhist
  · constructor
    · exact metaCICNormalizationFrontier_round_trip
    · constructor
      · intro x y heq
        exact metaCICNormalizationFrontierToEventFlow_injective heq
      · rfl

end BEDC.Derived.MetaCICNormalizationFrontierUp
