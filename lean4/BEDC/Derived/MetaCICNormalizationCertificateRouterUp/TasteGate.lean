import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICNormalizationCertificateRouterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICNormalizationCertificateRouterUp : Type where
  | mk :
      (auditAnchor candidateEvidence strongNormalization piAdequacy closedProjection
        authorizedGenerator compilerRecognizer kernelAcceptance transport route provenance
        name : BHist) →
      MetaCICNormalizationCertificateRouterUp
  deriving DecidableEq

def metaCICNormalizationCertificateRouterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICNormalizationCertificateRouterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICNormalizationCertificateRouterEncodeBHist h

def metaCICNormalizationCertificateRouterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICNormalizationCertificateRouterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICNormalizationCertificateRouterDecodeBHist tail)

private theorem metaCICNormalizationCertificateRouter_decode_encode_bhist :
    ∀ h : BHist,
      metaCICNormalizationCertificateRouterDecodeBHist
          (metaCICNormalizationCertificateRouterEncodeBHist h) =
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

private theorem metaCICNormalizationCertificateRouter_mk_congr
    {auditAnchor auditAnchor' candidateEvidence candidateEvidence' strongNormalization
      strongNormalization' piAdequacy piAdequacy' closedProjection closedProjection'
      authorizedGenerator authorizedGenerator' compilerRecognizer compilerRecognizer'
      kernelAcceptance kernelAcceptance' transport transport' route route' provenance
      provenance' name name' : BHist}
    (hAuditAnchor : auditAnchor' = auditAnchor)
    (hCandidateEvidence : candidateEvidence' = candidateEvidence)
    (hStrongNormalization : strongNormalization' = strongNormalization)
    (hPiAdequacy : piAdequacy' = piAdequacy)
    (hClosedProjection : closedProjection' = closedProjection)
    (hAuthorizedGenerator : authorizedGenerator' = authorizedGenerator)
    (hCompilerRecognizer : compilerRecognizer' = compilerRecognizer)
    (hKernelAcceptance : kernelAcceptance' = kernelAcceptance)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    MetaCICNormalizationCertificateRouterUp.mk auditAnchor' candidateEvidence'
        strongNormalization' piAdequacy' closedProjection' authorizedGenerator'
        compilerRecognizer' kernelAcceptance' transport' route' provenance' name' =
      MetaCICNormalizationCertificateRouterUp.mk auditAnchor candidateEvidence
        strongNormalization piAdequacy closedProjection authorizedGenerator compilerRecognizer
        kernelAcceptance transport route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hAuditAnchor
  cases hCandidateEvidence
  cases hStrongNormalization
  cases hPiAdequacy
  cases hClosedProjection
  cases hAuthorizedGenerator
  cases hCompilerRecognizer
  cases hKernelAcceptance
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

def metaCICNormalizationCertificateRouterFields :
    MetaCICNormalizationCertificateRouterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICNormalizationCertificateRouterUp.mk auditAnchor candidateEvidence
      strongNormalization piAdequacy closedProjection authorizedGenerator compilerRecognizer
      kernelAcceptance transport route provenance name =>
      [auditAnchor, candidateEvidence, strongNormalization, piAdequacy, closedProjection,
        authorizedGenerator, compilerRecognizer, kernelAcceptance, transport, route, provenance,
        name]

def metaCICNormalizationCertificateRouterToEventFlow :
    MetaCICNormalizationCertificateRouterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (metaCICNormalizationCertificateRouterFields x).map
        metaCICNormalizationCertificateRouterEncodeBHist

def metaCICNormalizationCertificateRouterFromEventFlow :
    EventFlow → Option MetaCICNormalizationCertificateRouterUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | auditAnchor :: rest0 =>
      match rest0 with
      | [] => none
      | candidateEvidence :: rest1 =>
          match rest1 with
          | [] => none
          | strongNormalization :: rest2 =>
              match rest2 with
              | [] => none
              | piAdequacy :: rest3 =>
                  match rest3 with
                  | [] => none
                  | closedProjection :: rest4 =>
                      match rest4 with
                      | [] => none
                      | authorizedGenerator :: rest5 =>
                          match rest5 with
                          | [] => none
                          | compilerRecognizer :: rest6 =>
                              match rest6 with
                              | [] => none
                              | kernelAcceptance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | transport :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | route :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | provenance :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | name :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (MetaCICNormalizationCertificateRouterUp.mk
                                                          (metaCICNormalizationCertificateRouterDecodeBHist
                                                            auditAnchor)
                                                          (metaCICNormalizationCertificateRouterDecodeBHist
                                                            candidateEvidence)
                                                          (metaCICNormalizationCertificateRouterDecodeBHist
                                                            strongNormalization)
                                                          (metaCICNormalizationCertificateRouterDecodeBHist
                                                            piAdequacy)
                                                          (metaCICNormalizationCertificateRouterDecodeBHist
                                                            closedProjection)
                                                          (metaCICNormalizationCertificateRouterDecodeBHist
                                                            authorizedGenerator)
                                                          (metaCICNormalizationCertificateRouterDecodeBHist
                                                            compilerRecognizer)
                                                          (metaCICNormalizationCertificateRouterDecodeBHist
                                                            kernelAcceptance)
                                                          (metaCICNormalizationCertificateRouterDecodeBHist
                                                            transport)
                                                          (metaCICNormalizationCertificateRouterDecodeBHist
                                                            route)
                                                          (metaCICNormalizationCertificateRouterDecodeBHist
                                                            provenance)
                                                          (metaCICNormalizationCertificateRouterDecodeBHist
                                                            name))
                                                  | _ :: _ => none

private theorem metaCICNormalizationCertificateRouter_round_trip :
    ∀ x : MetaCICNormalizationCertificateRouterUp,
      metaCICNormalizationCertificateRouterFromEventFlow
          (metaCICNormalizationCertificateRouterToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk auditAnchor candidateEvidence strongNormalization piAdequacy closedProjection
      authorizedGenerator compilerRecognizer kernelAcceptance transport route provenance name =>
      exact
        congrArg some
          (metaCICNormalizationCertificateRouter_mk_congr
            (metaCICNormalizationCertificateRouter_decode_encode_bhist auditAnchor)
            (metaCICNormalizationCertificateRouter_decode_encode_bhist candidateEvidence)
            (metaCICNormalizationCertificateRouter_decode_encode_bhist strongNormalization)
            (metaCICNormalizationCertificateRouter_decode_encode_bhist piAdequacy)
            (metaCICNormalizationCertificateRouter_decode_encode_bhist closedProjection)
            (metaCICNormalizationCertificateRouter_decode_encode_bhist authorizedGenerator)
            (metaCICNormalizationCertificateRouter_decode_encode_bhist compilerRecognizer)
            (metaCICNormalizationCertificateRouter_decode_encode_bhist kernelAcceptance)
            (metaCICNormalizationCertificateRouter_decode_encode_bhist transport)
            (metaCICNormalizationCertificateRouter_decode_encode_bhist route)
            (metaCICNormalizationCertificateRouter_decode_encode_bhist provenance)
            (metaCICNormalizationCertificateRouter_decode_encode_bhist name))

private theorem metaCICNormalizationCertificateRouterToEventFlow_injective
    {x y : MetaCICNormalizationCertificateRouterUp} :
    metaCICNormalizationCertificateRouterToEventFlow x =
        metaCICNormalizationCertificateRouterToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICNormalizationCertificateRouterFromEventFlow
          (metaCICNormalizationCertificateRouterToEventFlow x) =
        metaCICNormalizationCertificateRouterFromEventFlow
          (metaCICNormalizationCertificateRouterToEventFlow y) :=
    congrArg metaCICNormalizationCertificateRouterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICNormalizationCertificateRouter_round_trip x).symm
      (Eq.trans hread (metaCICNormalizationCertificateRouter_round_trip y)))

private theorem metaCICNormalizationCertificateRouter_field_faithful :
    ∀ x y : MetaCICNormalizationCertificateRouterUp,
      metaCICNormalizationCertificateRouterFields x =
          metaCICNormalizationCertificateRouterFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk auditAnchor candidateEvidence strongNormalization piAdequacy closedProjection
      authorizedGenerator compilerRecognizer kernelAcceptance transport route provenance name =>
      cases y with
      | mk auditAnchor' candidateEvidence' strongNormalization' piAdequacy' closedProjection'
          authorizedGenerator' compilerRecognizer' kernelAcceptance' transport' route'
          provenance' name' =>
          cases hfields
          rfl

instance metaCICNormalizationCertificateRouterBHistCarrier :
    BHistCarrier MetaCICNormalizationCertificateRouterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICNormalizationCertificateRouterToEventFlow
  fromEventFlow := metaCICNormalizationCertificateRouterFromEventFlow

instance taste_gate :
    ChapterTasteGate MetaCICNormalizationCertificateRouterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICNormalizationCertificateRouterFromEventFlow
          (metaCICNormalizationCertificateRouterToEventFlow x) =
        some x
    exact metaCICNormalizationCertificateRouter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICNormalizationCertificateRouterToEventFlow_injective heq)

instance metaCICNormalizationCertificateRouterFieldFaithful :
    FieldFaithful MetaCICNormalizationCertificateRouterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICNormalizationCertificateRouterFields
  field_faithful := metaCICNormalizationCertificateRouter_field_faithful

instance metaCICNormalizationCertificateRouterNontrivial :
    Nontrivial MetaCICNormalizationCertificateRouterUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICNormalizationCertificateRouterUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      MetaCICNormalizationCertificateRouterUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem MetaCICNormalizationCertificateRouterTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metaCICNormalizationCertificateRouterDecodeBHist
          (metaCICNormalizationCertificateRouterEncodeBHist h) =
        h) ∧
      (∀ x : MetaCICNormalizationCertificateRouterUp,
        metaCICNormalizationCertificateRouterFromEventFlow
            (metaCICNormalizationCertificateRouterToEventFlow x) =
          some x) ∧
        (∀ x y : MetaCICNormalizationCertificateRouterUp,
          metaCICNormalizationCertificateRouterToEventFlow x =
              metaCICNormalizationCertificateRouterToEventFlow y →
            x = y) ∧
          metaCICNormalizationCertificateRouterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metaCICNormalizationCertificateRouter_decode_encode_bhist
  · constructor
    · exact metaCICNormalizationCertificateRouter_round_trip
    · constructor
      · intro x y heq
        exact metaCICNormalizationCertificateRouterToEventFlow_injective heq
      · rfl

end BEDC.Derived.MetaCICNormalizationCertificateRouterUp
