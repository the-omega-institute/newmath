import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICNormalizationCertificateRouterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICNormalizationCertificateRouterUp : Type where
  | mk :
      (auditMap candidateEvidence strongNormalization piAppAdequacy closedProjection
        authorizedGenerator compilerRecognizer kernelAcceptance transport routeReplay
        provenance localName : BHist) →
      MetaCICNormalizationCertificateRouterUp
  deriving DecidableEq

private def metaCICNormalizationCertificateRouterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICNormalizationCertificateRouterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICNormalizationCertificateRouterEncodeBHist h

private def metaCICNormalizationCertificateRouterDecodeBHist : RawEvent → BHist
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
    {auditMap auditMap' candidateEvidence candidateEvidence'
      strongNormalization strongNormalization' piAppAdequacy piAppAdequacy'
      closedProjection closedProjection' authorizedGenerator authorizedGenerator'
      compilerRecognizer compilerRecognizer' kernelAcceptance kernelAcceptance'
      transport transport' routeReplay routeReplay' provenance provenance'
      localName localName' : BHist}
    (hAuditMap : auditMap' = auditMap)
    (hCandidateEvidence : candidateEvidence' = candidateEvidence)
    (hStrongNormalization : strongNormalization' = strongNormalization)
    (hPiAppAdequacy : piAppAdequacy' = piAppAdequacy)
    (hClosedProjection : closedProjection' = closedProjection)
    (hAuthorizedGenerator : authorizedGenerator' = authorizedGenerator)
    (hCompilerRecognizer : compilerRecognizer' = compilerRecognizer)
    (hKernelAcceptance : kernelAcceptance' = kernelAcceptance)
    (hTransport : transport' = transport)
    (hRouteReplay : routeReplay' = routeReplay)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    MetaCICNormalizationCertificateRouterUp.mk auditMap' candidateEvidence'
        strongNormalization' piAppAdequacy' closedProjection' authorizedGenerator'
        compilerRecognizer' kernelAcceptance' transport' routeReplay' provenance'
        localName' =
      MetaCICNormalizationCertificateRouterUp.mk auditMap candidateEvidence
        strongNormalization piAppAdequacy closedProjection authorizedGenerator
        compilerRecognizer kernelAcceptance transport routeReplay provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hAuditMap
  cases hCandidateEvidence
  cases hStrongNormalization
  cases hPiAppAdequacy
  cases hClosedProjection
  cases hAuthorizedGenerator
  cases hCompilerRecognizer
  cases hKernelAcceptance
  cases hTransport
  cases hRouteReplay
  cases hProvenance
  cases hLocalName
  rfl

private def metaCICNormalizationCertificateRouterToEventFlow :
    MetaCICNormalizationCertificateRouterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICNormalizationCertificateRouterUp.mk auditMap candidateEvidence
      strongNormalization piAppAdequacy closedProjection authorizedGenerator
      compilerRecognizer kernelAcceptance transport routeReplay provenance localName =>
      [[BMark.b0],
        metaCICNormalizationCertificateRouterEncodeBHist auditMap,
        metaCICNormalizationCertificateRouterEncodeBHist candidateEvidence,
        metaCICNormalizationCertificateRouterEncodeBHist strongNormalization,
        metaCICNormalizationCertificateRouterEncodeBHist piAppAdequacy,
        metaCICNormalizationCertificateRouterEncodeBHist closedProjection,
        metaCICNormalizationCertificateRouterEncodeBHist authorizedGenerator,
        metaCICNormalizationCertificateRouterEncodeBHist compilerRecognizer,
        metaCICNormalizationCertificateRouterEncodeBHist kernelAcceptance,
        metaCICNormalizationCertificateRouterEncodeBHist transport,
        metaCICNormalizationCertificateRouterEncodeBHist routeReplay,
        metaCICNormalizationCertificateRouterEncodeBHist provenance,
        metaCICNormalizationCertificateRouterEncodeBHist localName]

private def metaCICNormalizationCertificateRouterFromEventFlow :
    EventFlow → Option MetaCICNormalizationCertificateRouterUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag :: auditMap :: candidateEvidence :: strongNormalization :: piAppAdequacy ::
      closedProjection :: authorizedGenerator :: compilerRecognizer :: kernelAcceptance ::
      transport :: routeReplay :: provenance :: localName :: [] =>
      some
        (MetaCICNormalizationCertificateRouterUp.mk
          (metaCICNormalizationCertificateRouterDecodeBHist auditMap)
          (metaCICNormalizationCertificateRouterDecodeBHist candidateEvidence)
          (metaCICNormalizationCertificateRouterDecodeBHist strongNormalization)
          (metaCICNormalizationCertificateRouterDecodeBHist piAppAdequacy)
          (metaCICNormalizationCertificateRouterDecodeBHist closedProjection)
          (metaCICNormalizationCertificateRouterDecodeBHist authorizedGenerator)
          (metaCICNormalizationCertificateRouterDecodeBHist compilerRecognizer)
          (metaCICNormalizationCertificateRouterDecodeBHist kernelAcceptance)
          (metaCICNormalizationCertificateRouterDecodeBHist transport)
          (metaCICNormalizationCertificateRouterDecodeBHist routeReplay)
          (metaCICNormalizationCertificateRouterDecodeBHist provenance)
          (metaCICNormalizationCertificateRouterDecodeBHist localName))
  | _ => none

private theorem metaCICNormalizationCertificateRouter_round_trip :
    ∀ x : MetaCICNormalizationCertificateRouterUp,
      metaCICNormalizationCertificateRouterFromEventFlow
          (metaCICNormalizationCertificateRouterToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk auditMap candidateEvidence strongNormalization piAppAdequacy closedProjection
      authorizedGenerator compilerRecognizer kernelAcceptance transport routeReplay provenance
      localName =>
      change
        some
          (MetaCICNormalizationCertificateRouterUp.mk
            (metaCICNormalizationCertificateRouterDecodeBHist
              (metaCICNormalizationCertificateRouterEncodeBHist auditMap))
            (metaCICNormalizationCertificateRouterDecodeBHist
              (metaCICNormalizationCertificateRouterEncodeBHist candidateEvidence))
            (metaCICNormalizationCertificateRouterDecodeBHist
              (metaCICNormalizationCertificateRouterEncodeBHist strongNormalization))
            (metaCICNormalizationCertificateRouterDecodeBHist
              (metaCICNormalizationCertificateRouterEncodeBHist piAppAdequacy))
            (metaCICNormalizationCertificateRouterDecodeBHist
              (metaCICNormalizationCertificateRouterEncodeBHist closedProjection))
            (metaCICNormalizationCertificateRouterDecodeBHist
              (metaCICNormalizationCertificateRouterEncodeBHist authorizedGenerator))
            (metaCICNormalizationCertificateRouterDecodeBHist
              (metaCICNormalizationCertificateRouterEncodeBHist compilerRecognizer))
            (metaCICNormalizationCertificateRouterDecodeBHist
              (metaCICNormalizationCertificateRouterEncodeBHist kernelAcceptance))
            (metaCICNormalizationCertificateRouterDecodeBHist
              (metaCICNormalizationCertificateRouterEncodeBHist transport))
            (metaCICNormalizationCertificateRouterDecodeBHist
              (metaCICNormalizationCertificateRouterEncodeBHist routeReplay))
            (metaCICNormalizationCertificateRouterDecodeBHist
              (metaCICNormalizationCertificateRouterEncodeBHist provenance))
            (metaCICNormalizationCertificateRouterDecodeBHist
              (metaCICNormalizationCertificateRouterEncodeBHist localName))) =
          some
            (MetaCICNormalizationCertificateRouterUp.mk auditMap candidateEvidence
              strongNormalization piAppAdequacy closedProjection authorizedGenerator
              compilerRecognizer kernelAcceptance transport routeReplay provenance localName)
      exact
        congrArg some
          (metaCICNormalizationCertificateRouter_mk_congr
            (metaCICNormalizationCertificateRouter_decode_encode_bhist auditMap)
            (metaCICNormalizationCertificateRouter_decode_encode_bhist candidateEvidence)
            (metaCICNormalizationCertificateRouter_decode_encode_bhist strongNormalization)
            (metaCICNormalizationCertificateRouter_decode_encode_bhist piAppAdequacy)
            (metaCICNormalizationCertificateRouter_decode_encode_bhist closedProjection)
            (metaCICNormalizationCertificateRouter_decode_encode_bhist authorizedGenerator)
            (metaCICNormalizationCertificateRouter_decode_encode_bhist compilerRecognizer)
            (metaCICNormalizationCertificateRouter_decode_encode_bhist kernelAcceptance)
            (metaCICNormalizationCertificateRouter_decode_encode_bhist transport)
            (metaCICNormalizationCertificateRouter_decode_encode_bhist routeReplay)
            (metaCICNormalizationCertificateRouter_decode_encode_bhist provenance)
            (metaCICNormalizationCertificateRouter_decode_encode_bhist localName))

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

instance metaCICNormalizationCertificateRouterBHistCarrier :
    BHistCarrier MetaCICNormalizationCertificateRouterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICNormalizationCertificateRouterToEventFlow
  fromEventFlow := metaCICNormalizationCertificateRouterFromEventFlow

instance metaCICNormalizationCertificateRouterChapterTasteGate :
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
  fields := fun x =>
    match x with
    | MetaCICNormalizationCertificateRouterUp.mk auditMap candidateEvidence
        strongNormalization piAppAdequacy closedProjection authorizedGenerator
        compilerRecognizer kernelAcceptance transport routeReplay provenance localName =>
        [auditMap, candidateEvidence, strongNormalization, piAppAdequacy, closedProjection,
          authorizedGenerator, compilerRecognizer, kernelAcceptance, transport, routeReplay,
          provenance, localName]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk auditMap candidateEvidence strongNormalization piAppAdequacy closedProjection
        authorizedGenerator compilerRecognizer kernelAcceptance transport routeReplay provenance
        localName =>
        cases y with
        | mk auditMap' candidateEvidence' strongNormalization' piAppAdequacy'
            closedProjection' authorizedGenerator' compilerRecognizer' kernelAcceptance'
            transport' routeReplay' provenance' localName' =>
            cases hfields
            rfl

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

theorem MetaCICNormalizationCertificateRouterUp_single_carrier_alignment :
    (∀ h : BHist,
      metaCICNormalizationCertificateRouterDecodeBHist
          (metaCICNormalizationCertificateRouterEncodeBHist h) =
        h) ∧
      (∀ auditMap candidateEvidence strongNormalization piAppAdequacy closedProjection
          authorizedGenerator compilerRecognizer kernelAcceptance transport routeReplay
          provenance localName : BHist,
        metaCICNormalizationCertificateRouterToEventFlow
            (MetaCICNormalizationCertificateRouterUp.mk auditMap candidateEvidence
              strongNormalization piAppAdequacy closedProjection authorizedGenerator
              compilerRecognizer kernelAcceptance transport routeReplay provenance localName) =
          [[BMark.b0],
            metaCICNormalizationCertificateRouterEncodeBHist auditMap,
            metaCICNormalizationCertificateRouterEncodeBHist candidateEvidence,
            metaCICNormalizationCertificateRouterEncodeBHist strongNormalization,
            metaCICNormalizationCertificateRouterEncodeBHist piAppAdequacy,
            metaCICNormalizationCertificateRouterEncodeBHist closedProjection,
            metaCICNormalizationCertificateRouterEncodeBHist authorizedGenerator,
            metaCICNormalizationCertificateRouterEncodeBHist compilerRecognizer,
            metaCICNormalizationCertificateRouterEncodeBHist kernelAcceptance,
            metaCICNormalizationCertificateRouterEncodeBHist transport,
            metaCICNormalizationCertificateRouterEncodeBHist routeReplay,
            metaCICNormalizationCertificateRouterEncodeBHist provenance,
            metaCICNormalizationCertificateRouterEncodeBHist localName]) ∧
        (∃ x y : MetaCICNormalizationCertificateRouterUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    exact metaCICNormalizationCertificateRouter_decode_encode_bhist h
  · constructor
    · intro auditMap candidateEvidence strongNormalization piAppAdequacy closedProjection
        authorizedGenerator compilerRecognizer kernelAcceptance transport routeReplay provenance
        localName
      rfl
    · exact
        ⟨MetaCICNormalizationCertificateRouterUp.mk BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty,
          MetaCICNormalizationCertificateRouterUp.mk (BHist.e0 BHist.Empty) BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty,
          by
            intro h
            cases h⟩

def MetaCICNormalizationCertificateRouterPacket [AskSetup] [PackageSetup]
    (audit candidate strongNorm piApp closedProjection generator compiler kernelAccept transport
      replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  UnaryHistory audit ∧ UnaryHistory candidate ∧ UnaryHistory strongNorm ∧
    UnaryHistory piApp ∧ UnaryHistory closedProjection ∧ UnaryHistory generator ∧
      UnaryHistory compiler ∧ UnaryHistory kernelAccept ∧ UnaryHistory transport ∧
        UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
          Cont candidate strongNorm piApp ∧ Cont piApp closedProjection transport ∧
            Cont generator compiler kernelAccept ∧ Cont transport replay provenance ∧
              PkgSig bundle localName pkg

theorem MetaCICNormalizationCertificateRouterClosedReadRefusal [AskSetup] [PackageSetup]
    {audit candidate strongNorm piApp closedProjection generator compiler kernelAccept transport
      replay provenance localName closedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationCertificateRouterPacket audit candidate strongNorm piApp
        closedProjection generator compiler kernelAccept transport replay provenance localName
        bundle pkg →
      Cont candidate closedProjection closedRead →
        UnaryHistory candidate ∧ UnaryHistory closedProjection ∧ UnaryHistory closedRead ∧
          Cont candidate closedProjection closedRead ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet closedRoute
  obtain ⟨_auditUnary, candidateUnary, _strongNormUnary, _piAppUnary, closedProjectionUnary,
    _generatorUnary, _compilerUnary, _kernelAcceptUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _candidateStrongNorm, _piAppProjection,
    _producerAcceptance, _transportReplay, pkgSig⟩ := packet
  have closedReadUnary : UnaryHistory closedRead :=
    unary_cont_closed candidateUnary closedProjectionUnary closedRoute
  exact ⟨candidateUnary, closedProjectionUnary, closedReadUnary, closedRoute, pkgSig⟩

end BEDC.Derived.MetaCICNormalizationCertificateRouterUp
