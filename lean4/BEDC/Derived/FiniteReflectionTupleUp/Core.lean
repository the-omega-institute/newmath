import BEDC.Derived.FiniteReflectionTupleUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteReflectionTupleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

def FiniteReflectionTupleCarrier [AskSetup] [PackageSetup]
    (candidate stability admission compiler image readback transport replay provenance request
      localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory candidate ∧ UnaryHistory stability ∧ UnaryHistory admission ∧
    UnaryHistory compiler ∧ UnaryHistory image ∧ UnaryHistory readback ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory request ∧ UnaryHistory localCert ∧
          Cont candidate stability admission ∧ Cont admission compiler image ∧
            Cont image readback transport ∧ Cont transport replay provenance ∧
              Cont provenance request localCert ∧ PkgSig bundle localCert pkg

theorem FiniteReflectionTupleCarrier_image_readback_exactness
    [AskSetup] [PackageSetup]
    {candidate stability admission compiler image readback transport replay provenance request
      localCert candidate' stability' admission' compiler' image' readback' transport' replay'
      provenance' request' localCert' publicRead publicRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteReflectionTupleCarrier candidate stability admission compiler image readback transport
        replay provenance request localCert bundle pkg ->
      FiniteReflectionTupleCarrier candidate' stability' admission' compiler' image' readback'
          transport' replay' provenance' request' localCert' bundle pkg ->
        hsame image image' ->
          hsame readback readback' ->
            Cont image readback publicRead ->
              Cont image' readback' publicRead' ->
                PkgSig bundle publicRead pkg ->
                  PkgSig bundle publicRead' pkg ->
                    hsame publicRead publicRead' ∧ UnaryHistory publicRead ∧
                      UnaryHistory publicRead' ∧ Cont image readback publicRead ∧
                        Cont image' readback' publicRead' ∧
                          PkgSig bundle publicRead pkg ∧
                            PkgSig bundle publicRead' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier carrier' sameImage sameReadback imageReadbackPublic imageReadbackPublic'
    publicPkg publicPkg'
  obtain ⟨_candidateUnary, _stabilityUnary, _admissionUnary, _compilerUnary, imageUnary,
    readbackUnary, _transportUnary, _replayUnary, _provenanceUnary, _requestUnary,
    _localCertUnary, _candidateStabilityAdmission, _admissionCompilerImage,
    _imageReadbackTransport, _transportReplayProvenance, _provenanceRequestLocalCert,
    _localCertPkg⟩ := carrier
  obtain ⟨_candidateUnary', _stabilityUnary', _admissionUnary', _compilerUnary', imageUnary',
    readbackUnary', _transportUnary', _replayUnary', _provenanceUnary', _requestUnary',
    _localCertUnary', _candidateStabilityAdmission', _admissionCompilerImage',
    _imageReadbackTransport', _transportReplayProvenance', _provenanceRequestLocalCert',
    _localCertPkg'⟩ := carrier'
  have samePublic : hsame publicRead publicRead' :=
    cont_respects_hsame sameImage sameReadback imageReadbackPublic imageReadbackPublic'
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed imageUnary readbackUnary imageReadbackPublic
  have publicUnary' : UnaryHistory publicRead' :=
    unary_cont_closed imageUnary' readbackUnary' imageReadbackPublic'
  exact
    ⟨samePublic, publicUnary, publicUnary', imageReadbackPublic, imageReadbackPublic',
      publicPkg, publicPkg'⟩

theorem FiniteReflectionTupleCarrier_request_exhaustion
    [AskSetup] [PackageSetup]
    {candidate stability admission compiler image readback transport replay provenance request
      localCert bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteReflectionTupleCarrier candidate stability admission compiler image readback transport
        replay provenance request localCert bundle pkg ->
      Cont provenance request bridgeRead ->
        PkgSig bundle bridgeRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                FiniteReflectionTupleCarrier candidate stability admission compiler image readback
                  transport replay provenance request localCert bundle pkg ∧ hsame row bridgeRead)
              (fun row : BHist =>
                Cont image readback transport ∧ Cont provenance request bridgeRead ∧
                  hsame row bridgeRead)
              (fun row : BHist => PkgSig bundle bridgeRead pkg ∧ hsame row bridgeRead)
              hsame ∧
            UnaryHistory bridgeRead ∧ PkgSig bundle bridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier provenanceRequestBridge bridgePkg
  have carrierWitness := carrier
  obtain ⟨_candidateUnary, _stabilityUnary, _admissionUnary, _compilerUnary, _imageUnary,
    _readbackUnary, _transportUnary, _replayUnary, provenanceUnary, requestUnary,
    _localCertUnary, _candidateStabilityAdmission, _admissionCompilerImage,
    imageReadbackTransport, _transportReplayProvenance, _provenanceRequestLocalCert,
    _localCertPkg⟩ := carrier
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed provenanceUnary requestUnary provenanceRequestBridge
  have certCore :
      NameCert
        (fun row : BHist =>
          FiniteReflectionTupleCarrier candidate stability admission compiler image readback
            transport replay provenance request localCert bundle pkg ∧ hsame row bridgeRead)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro bridgeRead
        (And.intro carrierWitness (hsame_refl bridgeRead))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
  have semantic :
      SemanticNameCert
          (fun row : BHist =>
            FiniteReflectionTupleCarrier candidate stability admission compiler image readback
              transport replay provenance request localCert bundle pkg ∧ hsame row bridgeRead)
          (fun row : BHist =>
            Cont image readback transport ∧ Cont provenance request bridgeRead ∧
              hsame row bridgeRead)
          (fun row : BHist => PkgSig bundle bridgeRead pkg ∧ hsame row bridgeRead)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro _row sourceRow
        exact ⟨imageReadbackTransport, provenanceRequestBridge, sourceRow.right⟩
      ledger_sound := by
        intro _row sourceRow
        exact ⟨bridgePkg, sourceRow.right⟩
    }
  exact ⟨semantic, bridgeUnary, bridgePkg⟩

theorem FiniteReflectionTupleCarrier_public_projection_route
    [AskSetup] [PackageSetup]
    {candidate stability admission compiler image readback transport replay provenance request
      localCert publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteReflectionTupleCarrier candidate stability admission compiler image readback transport
        replay provenance request localCert bundle pkg →
      Cont image readback publicRead →
        PkgSig bundle publicRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                FiniteReflectionTupleCarrier candidate stability admission compiler image readback
                  transport replay provenance request localCert bundle pkg ∧ hsame row publicRead)
              (fun row : BHist => Cont image readback publicRead ∧ hsame row publicRead)
              (fun row : BHist => PkgSig bundle publicRead pkg ∧ hsame row publicRead)
              hsame ∧
            UnaryHistory publicRead ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier imageReadbackPublic publicPkg
  have carrierWitness := carrier
  obtain ⟨_candidateUnary, _stabilityUnary, _admissionUnary, _compilerUnary, imageUnary,
    readbackUnary, _transportUnary, _replayUnary, _provenanceUnary, _requestUnary,
    _localCertUnary, _candidateStabilityAdmission, _admissionCompilerImage,
    _imageReadbackTransport, _transportReplayProvenance, _provenanceRequestLocalCert,
    _localCertPkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed imageUnary readbackUnary imageReadbackPublic

  have certCore :
      NameCert
        (fun row : BHist =>
          FiniteReflectionTupleCarrier candidate stability admission compiler image readback
            transport replay provenance request localCert bundle pkg ∧ hsame row publicRead)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro publicRead
        (And.intro carrierWitness (hsame_refl publicRead))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
  have semantic :
      SemanticNameCert
          (fun row : BHist =>
            FiniteReflectionTupleCarrier candidate stability admission compiler image readback
              transport replay provenance request localCert bundle pkg ∧ hsame row publicRead)
          (fun row : BHist => Cont image readback publicRead ∧ hsame row publicRead)
          (fun row : BHist => PkgSig bundle publicRead pkg ∧ hsame row publicRead)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro _row sourceRow
        exact ⟨imageReadbackPublic, sourceRow.right⟩
      ledger_sound := by
        intro _row sourceRow
        exact ⟨publicPkg, sourceRow.right⟩
    }
  exact ⟨semantic, publicUnary, publicPkg⟩

theorem FiniteReflectionTupleCarrier_componentwise_transport
    [AskSetup] [PackageSetup]
    {candidate stability admission compiler image readback transport replay provenance request
      localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteReflectionTupleCarrier candidate stability admission compiler image readback transport
        replay provenance request localCert bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            FiniteReflectionTupleCarrier candidate stability admission compiler image readback
              transport replay provenance request localCert bundle pkg ∧ hsame row localCert)
          (fun row : BHist =>
            Cont transport replay provenance ∧ Cont provenance request localCert ∧
              hsame row localCert)
          (fun row : BHist => PkgSig bundle localCert pkg ∧ hsame row localCert)
          hsame ∧
        UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
          UnaryHistory request ∧ UnaryHistory localCert ∧ Cont transport replay provenance ∧
            Cont provenance request localCert ∧ PkgSig bundle localCert pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier
  have carrierWitness := carrier
  obtain ⟨_candidateUnary, _stabilityUnary, _admissionUnary, _compilerUnary, _imageUnary,
    _readbackUnary, transportUnary, replayUnary, provenanceUnary, requestUnary, localCertUnary,
    _candidateStabilityAdmission, _admissionCompilerImage, _imageReadbackTransport,
    transportReplayProvenance, provenanceRequestLocalCert, localCertPkg⟩ := carrier
  have certCore :
      NameCert
        (fun row : BHist =>
          FiniteReflectionTupleCarrier candidate stability admission compiler image readback
            transport replay provenance request localCert bundle pkg ∧ hsame row localCert)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro localCert
        (And.intro carrierWitness (hsame_refl localCert))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
  have semantic :
      SemanticNameCert
          (fun row : BHist =>
            FiniteReflectionTupleCarrier candidate stability admission compiler image readback
              transport replay provenance request localCert bundle pkg ∧ hsame row localCert)
          (fun row : BHist =>
            Cont transport replay provenance ∧ Cont provenance request localCert ∧
              hsame row localCert)
          (fun row : BHist => PkgSig bundle localCert pkg ∧ hsame row localCert)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro _row sourceRow
        exact ⟨transportReplayProvenance, provenanceRequestLocalCert, sourceRow.right⟩
      ledger_sound := by
        intro _row sourceRow
        exact ⟨localCertPkg, sourceRow.right⟩
    }
  exact
    ⟨semantic, transportUnary, replayUnary, provenanceUnary, requestUnary, localCertUnary,
      transportReplayProvenance, provenanceRequestLocalCert, localCertPkg⟩

theorem FiniteReflectionTupleCarrier_dependency_ledger_totality
    [AskSetup] [PackageSetup]
    {candidate stability admission compiler image readback transport replay provenance request
      localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteReflectionTupleCarrier candidate stability admission compiler image readback transport
        replay provenance request localCert bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            FiniteReflectionTupleCarrier candidate stability admission compiler image readback
              transport replay provenance request localCert bundle pkg ∧ hsame row localCert)
          (fun row : BHist =>
            Cont candidate stability admission ∧ Cont admission compiler image ∧
              Cont image readback transport ∧ Cont transport replay provenance ∧
                Cont provenance request localCert ∧ hsame row localCert)
          (fun row : BHist => PkgSig bundle localCert pkg ∧ hsame row localCert)
          hsame ∧
        UnaryHistory candidate ∧ UnaryHistory stability ∧ UnaryHistory admission ∧
          UnaryHistory compiler ∧ UnaryHistory image ∧ UnaryHistory readback ∧
            UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
              UnaryHistory request ∧ UnaryHistory localCert ∧ PkgSig bundle localCert pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier
  have carrierWitness := carrier
  obtain ⟨candidateUnary, stabilityUnary, admissionUnary, compilerUnary, imageUnary,
    readbackUnary, transportUnary, replayUnary, provenanceUnary, requestUnary, localCertUnary,
    candidateStabilityAdmission, admissionCompilerImage, imageReadbackTransport,
    transportReplayProvenance, provenanceRequestLocalCert, localCertPkg⟩ := carrier
  have certCore :
      NameCert
        (fun row : BHist =>
          FiniteReflectionTupleCarrier candidate stability admission compiler image readback
            transport replay provenance request localCert bundle pkg ∧ hsame row localCert)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro localCert
        (And.intro carrierWitness (hsame_refl localCert))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
  have semantic :
      SemanticNameCert
          (fun row : BHist =>
            FiniteReflectionTupleCarrier candidate stability admission compiler image readback
              transport replay provenance request localCert bundle pkg ∧ hsame row localCert)
          (fun row : BHist =>
            Cont candidate stability admission ∧ Cont admission compiler image ∧
              Cont image readback transport ∧ Cont transport replay provenance ∧
                Cont provenance request localCert ∧ hsame row localCert)
          (fun row : BHist => PkgSig bundle localCert pkg ∧ hsame row localCert)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro _row sourceRow
        exact
          ⟨candidateStabilityAdmission, admissionCompilerImage, imageReadbackTransport,
            transportReplayProvenance, provenanceRequestLocalCert, sourceRow.right⟩
      ledger_sound := by
        intro _row sourceRow
        exact ⟨localCertPkg, sourceRow.right⟩
    }
  exact
    ⟨semantic, candidateUnary, stabilityUnary, admissionUnary, compilerUnary, imageUnary,
      readbackUnary, transportUnary, replayUnary, provenanceUnary, requestUnary, localCertUnary,
      localCertPkg⟩

theorem FiniteReflectionTupleCarrier_audit_result_nonescape
    [AskSetup] [PackageSetup]
    {candidate stability admission compiler image readback transport replay provenance request
      localCert auditRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteReflectionTupleCarrier candidate stability admission compiler image readback transport
        replay provenance request localCert bundle pkg →
      Cont image readback auditRead →
        Cont provenance request bridgeRead →
          PkgSig bundle auditRead pkg →
            PkgSig bundle bridgeRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    FiniteReflectionTupleCarrier candidate stability admission compiler image
                      readback transport replay provenance request localCert bundle pkg ∧
                      hsame row auditRead)
                  (fun row : BHist =>
                    Cont image readback auditRead ∧ Cont provenance request bridgeRead ∧
                      hsame row auditRead)
                  (fun row : BHist =>
                    PkgSig bundle auditRead pkg ∧ PkgSig bundle bridgeRead pkg ∧
                      hsame row auditRead)
                  hsame ∧
                UnaryHistory auditRead ∧ UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier imageReadbackAudit provenanceRequestBridge auditPkg bridgePkg
  have carrierWitness := carrier
  obtain ⟨_candidateUnary, _stabilityUnary, _admissionUnary, _compilerUnary, imageUnary,
    readbackUnary, _transportUnary, _replayUnary, provenanceUnary, requestUnary,
    _localCertUnary, _candidateStabilityAdmission, _admissionCompilerImage,
    _imageReadbackTransport, _transportReplayProvenance, _provenanceRequestLocalCert,
    _localCertPkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed imageUnary readbackUnary imageReadbackAudit
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed provenanceUnary requestUnary provenanceRequestBridge
  have certCore :
      NameCert
        (fun row : BHist =>
          FiniteReflectionTupleCarrier candidate stability admission compiler image readback
            transport replay provenance request localCert bundle pkg ∧ hsame row auditRead)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro auditRead
        (And.intro carrierWitness (hsame_refl auditRead))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
  have semantic :
      SemanticNameCert
          (fun row : BHist =>
            FiniteReflectionTupleCarrier candidate stability admission compiler image readback
              transport replay provenance request localCert bundle pkg ∧ hsame row auditRead)
          (fun row : BHist =>
            Cont image readback auditRead ∧ Cont provenance request bridgeRead ∧
              hsame row auditRead)
          (fun row : BHist =>
            PkgSig bundle auditRead pkg ∧ PkgSig bundle bridgeRead pkg ∧
              hsame row auditRead)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro _row sourceRow
        exact ⟨imageReadbackAudit, provenanceRequestBridge, sourceRow.right⟩
      ledger_sound := by
        intro _row sourceRow
        exact ⟨auditPkg, bridgePkg, sourceRow.right⟩
    }
  exact ⟨semantic, auditUnary, bridgeUnary⟩

end BEDC.Derived.FiniteReflectionTupleUp
