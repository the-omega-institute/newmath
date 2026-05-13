import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TranscendentalSupplyInscriptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TranscendentalSupplyInscriptionUp : Type where
  | mk :
      (supply closedSystem inscription gap transport routes provenance nameCert : BHist) →
      TranscendentalSupplyInscriptionUp
  deriving DecidableEq

private def transcendentalSupplyInscriptionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: transcendentalSupplyInscriptionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: transcendentalSupplyInscriptionEncodeBHist h

private def transcendentalSupplyInscriptionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (transcendentalSupplyInscriptionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (transcendentalSupplyInscriptionDecodeBHist tail)

private theorem transcendentalSupplyInscriptionDecode_encode_bhist :
    ∀ h : BHist,
      transcendentalSupplyInscriptionDecodeBHist
        (transcendentalSupplyInscriptionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem transcendentalSupplyInscription_mk_congr
    {supply supply' closedSystem closedSystem' inscription inscription' gap gap'
      transport transport' routes routes' provenance provenance' nameCert nameCert' : BHist}
    (hSupply : supply' = supply)
    (hClosedSystem : closedSystem' = closedSystem)
    (hInscription : inscription' = inscription)
    (hGap : gap' = gap)
    (hTransport : transport' = transport)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    TranscendentalSupplyInscriptionUp.mk supply' closedSystem' inscription' gap' transport'
        routes' provenance' nameCert' =
      TranscendentalSupplyInscriptionUp.mk supply closedSystem inscription gap transport routes
        provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSupply
  cases hClosedSystem
  cases hInscription
  cases hGap
  cases hTransport
  cases hRoutes
  cases hProvenance
  cases hNameCert
  rfl

private def transcendentalSupplyInscriptionToEventFlow :
    TranscendentalSupplyInscriptionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TranscendentalSupplyInscriptionUp.mk supply closedSystem inscription gap transport routes
      provenance nameCert =>
      [[BMark.b0],
        transcendentalSupplyInscriptionEncodeBHist supply,
        [BMark.b1, BMark.b0],
        transcendentalSupplyInscriptionEncodeBHist closedSystem,
        [BMark.b1, BMark.b1, BMark.b0],
        transcendentalSupplyInscriptionEncodeBHist inscription,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        transcendentalSupplyInscriptionEncodeBHist gap,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        transcendentalSupplyInscriptionEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        transcendentalSupplyInscriptionEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        transcendentalSupplyInscriptionEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        transcendentalSupplyInscriptionEncodeBHist nameCert]

private def transcendentalSupplyInscriptionFromEventFlow :
    EventFlow → Option TranscendentalSupplyInscriptionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | supply :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | closedSystem :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | inscription :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | gap :: rest7 =>
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
                                              | routes :: rest11 =>
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
                                                              | nameCert :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (TranscendentalSupplyInscriptionUp.mk
                                                                          (transcendentalSupplyInscriptionDecodeBHist supply)
                                                                          (transcendentalSupplyInscriptionDecodeBHist closedSystem)
                                                                          (transcendentalSupplyInscriptionDecodeBHist inscription)
                                                                          (transcendentalSupplyInscriptionDecodeBHist gap)
                                                                          (transcendentalSupplyInscriptionDecodeBHist transport)
                                                                          (transcendentalSupplyInscriptionDecodeBHist routes)
                                                                          (transcendentalSupplyInscriptionDecodeBHist provenance)
                                                                          (transcendentalSupplyInscriptionDecodeBHist nameCert))
                                                                  | _ :: _ => none

private theorem transcendentalSupplyInscription_round_trip :
    ∀ x : TranscendentalSupplyInscriptionUp,
      transcendentalSupplyInscriptionFromEventFlow
          (transcendentalSupplyInscriptionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk supply closedSystem inscription gap transport routes provenance nameCert =>
      change
        some
          (TranscendentalSupplyInscriptionUp.mk
            (transcendentalSupplyInscriptionDecodeBHist
              (transcendentalSupplyInscriptionEncodeBHist supply))
            (transcendentalSupplyInscriptionDecodeBHist
              (transcendentalSupplyInscriptionEncodeBHist closedSystem))
            (transcendentalSupplyInscriptionDecodeBHist
              (transcendentalSupplyInscriptionEncodeBHist inscription))
            (transcendentalSupplyInscriptionDecodeBHist
              (transcendentalSupplyInscriptionEncodeBHist gap))
            (transcendentalSupplyInscriptionDecodeBHist
              (transcendentalSupplyInscriptionEncodeBHist transport))
            (transcendentalSupplyInscriptionDecodeBHist
              (transcendentalSupplyInscriptionEncodeBHist routes))
            (transcendentalSupplyInscriptionDecodeBHist
              (transcendentalSupplyInscriptionEncodeBHist provenance))
            (transcendentalSupplyInscriptionDecodeBHist
              (transcendentalSupplyInscriptionEncodeBHist nameCert))) =
          some
            (TranscendentalSupplyInscriptionUp.mk supply closedSystem inscription gap transport
              routes provenance nameCert)
      exact
        congrArg some
          (transcendentalSupplyInscription_mk_congr
            (transcendentalSupplyInscriptionDecode_encode_bhist supply)
            (transcendentalSupplyInscriptionDecode_encode_bhist closedSystem)
            (transcendentalSupplyInscriptionDecode_encode_bhist inscription)
            (transcendentalSupplyInscriptionDecode_encode_bhist gap)
            (transcendentalSupplyInscriptionDecode_encode_bhist transport)
            (transcendentalSupplyInscriptionDecode_encode_bhist routes)
            (transcendentalSupplyInscriptionDecode_encode_bhist provenance)
            (transcendentalSupplyInscriptionDecode_encode_bhist nameCert))

private theorem transcendentalSupplyInscriptionToEventFlow_injective
    {x y : TranscendentalSupplyInscriptionUp} :
    transcendentalSupplyInscriptionToEventFlow x =
      transcendentalSupplyInscriptionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      transcendentalSupplyInscriptionFromEventFlow
          (transcendentalSupplyInscriptionToEventFlow x) =
        transcendentalSupplyInscriptionFromEventFlow
          (transcendentalSupplyInscriptionToEventFlow y) :=
    congrArg transcendentalSupplyInscriptionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (transcendentalSupplyInscription_round_trip x).symm
      (Eq.trans hread (transcendentalSupplyInscription_round_trip y)))

instance transcendentalSupplyInscriptionBHistCarrier :
    BHistCarrier TranscendentalSupplyInscriptionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := transcendentalSupplyInscriptionToEventFlow
  fromEventFlow := transcendentalSupplyInscriptionFromEventFlow

instance transcendentalSupplyInscriptionChapterTasteGate :
    ChapterTasteGate TranscendentalSupplyInscriptionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      transcendentalSupplyInscriptionFromEventFlow
          (transcendentalSupplyInscriptionToEventFlow x) =
        some x
    exact transcendentalSupplyInscription_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (transcendentalSupplyInscriptionToEventFlow_injective heq)

theorem TranscendentalSupplyInscriptionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      transcendentalSupplyInscriptionDecodeBHist
        (transcendentalSupplyInscriptionEncodeBHist h) = h) ∧
      (∀ x : TranscendentalSupplyInscriptionUp,
        transcendentalSupplyInscriptionFromEventFlow
            (transcendentalSupplyInscriptionToEventFlow x) =
          some x) ∧
        (∀ x y : TranscendentalSupplyInscriptionUp,
          transcendentalSupplyInscriptionToEventFlow x =
            transcendentalSupplyInscriptionToEventFlow y → x = y) ∧
          transcendentalSupplyInscriptionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact transcendentalSupplyInscriptionDecode_encode_bhist
  · constructor
    · exact transcendentalSupplyInscription_round_trip
    · constructor
      · intro x y heq
        exact transcendentalSupplyInscriptionToEventFlow_injective heq
      · rfl

end BEDC.Derived.TranscendentalSupplyInscriptionUp
