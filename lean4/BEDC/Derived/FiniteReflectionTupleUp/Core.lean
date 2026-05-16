import BEDC.Derived.FiniteReflectionTupleUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteReflectionTupleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.FiniteReflectionTupleUp
