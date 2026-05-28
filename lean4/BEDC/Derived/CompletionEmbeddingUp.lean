import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompletionEmbeddingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CompletionEmbeddingCarrier [AskSetup] [PackageSetup]
    (sourceMetric completionTarget denseImage isometry regularCauchy hausdorffBoundary
      realSeal transport replay provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sourceMetric ∧ UnaryHistory completionTarget ∧ UnaryHistory denseImage ∧
    UnaryHistory isometry ∧ UnaryHistory regularCauchy ∧ UnaryHistory hausdorffBoundary ∧
      UnaryHistory realSeal ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localCert ∧
          Cont sourceMetric regularCauchy denseImage ∧
            Cont denseImage isometry realSeal ∧ PkgSig bundle provenance pkg ∧
              SemanticNameCert
                (fun row : BHist => hsame row localCert ∧ UnaryHistory row)
                (fun row : BHist => UnaryHistory row ∧ hsame row localCert)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
                (fun row row' : BHist => hsame row row')

theorem CompletionEmbeddingCarrier_dense_isometric_handoff [AskSetup] [PackageSetup]
    {sourceMetric completionTarget denseImage isometry regularCauchy hausdorffBoundary
      realSeal transport replay provenance localCert denseRead isoRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionEmbeddingCarrier sourceMetric completionTarget denseImage isometry regularCauchy
        hausdorffBoundary realSeal transport replay provenance localCert bundle pkg ->
      Cont regularCauchy denseImage denseRead ->
        Cont denseRead isometry isoRead ->
          Cont isoRead realSeal sealRead ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory denseRead ∧ UnaryHistory isoRead ∧ UnaryHistory sealRead ∧
                Cont regularCauchy denseImage denseRead ∧ Cont denseRead isometry isoRead ∧
                  Cont isoRead realSeal sealRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  intro carrier regularDense denseIso isoSeal sealPkg
  obtain ⟨_sourceMetricUnary, _completionTargetUnary, denseImageUnary, isometryUnary,
    regularCauchyUnary, _hausdorffBoundaryUnary, realSealUnary, _transportUnary,
      _replayUnary, _provenanceUnary, _localCertUnary, _sourceDense, _denseSeal,
        provenancePkg, _localSemantic⟩ := carrier
  have denseReadUnary : UnaryHistory denseRead :=
    unary_cont_closed regularCauchyUnary denseImageUnary regularDense
  have isoReadUnary : UnaryHistory isoRead :=
    unary_cont_closed denseReadUnary isometryUnary denseIso
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed isoReadUnary realSealUnary isoSeal
  exact
    ⟨denseReadUnary, isoReadUnary, sealReadUnary, regularDense, denseIso, isoSeal,
      provenancePkg, sealPkg⟩

theorem CompletionEmbeddingCarrier_real_seal_nonescape [AskSetup] [PackageSetup]
    {sourceMetric completionTarget denseImage isometry regularCauchy hausdorffBoundary
      realSeal transport replay provenance localCert endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionEmbeddingCarrier sourceMetric completionTarget denseImage isometry regularCauchy
        hausdorffBoundary realSeal transport replay provenance localCert bundle pkg ->
      Cont realSeal hausdorffBoundary endpointRead ->
        PkgSig bundle endpointRead pkg ->
          UnaryHistory realSeal ∧ UnaryHistory hausdorffBoundary ∧
            UnaryHistory endpointRead ∧ Cont denseImage isometry realSeal ∧
              Cont realSeal hausdorffBoundary endpointRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  intro carrier realBoundary endpointPkg
  obtain ⟨_sourceMetricUnary, _completionTargetUnary, denseImageUnary, isometryUnary,
    _regularCauchyUnary, hausdorffBoundaryUnary, realSealUnary, _transportUnary,
      _replayUnary, _provenanceUnary, _localCertUnary, _sourceDense, denseSeal,
        provenancePkg, _localSemantic⟩ := carrier
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed realSealUnary hausdorffBoundaryUnary realBoundary
  exact
    ⟨realSealUnary, hausdorffBoundaryUnary, endpointUnary, denseSeal, realBoundary,
      provenancePkg, endpointPkg⟩

theorem CompletionEmbeddingCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {sourceMetric completionTarget denseImage isometry regularCauchy hausdorffBoundary
      realSeal transport replay provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionEmbeddingCarrier sourceMetric completionTarget denseImage isometry regularCauchy
        hausdorffBoundary realSeal transport replay provenance localCert bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row localCert ∧ UnaryHistory row)
          (fun row : BHist => UnaryHistory row ∧ hsame row localCert)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
          (fun row row' : BHist => hsame row row') ∧
        UnaryHistory sourceMetric ∧ UnaryHistory completionTarget ∧ UnaryHistory denseImage ∧
          UnaryHistory isometry ∧ UnaryHistory regularCauchy ∧
            UnaryHistory hausdorffBoundary ∧ UnaryHistory realSeal ∧
              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist NameCert ProbeBundle Pkg
  intro carrier
  obtain ⟨sourceMetricUnary, completionTargetUnary, denseImageUnary, isometryUnary,
    regularCauchyUnary, hausdorffBoundaryUnary, realSealUnary, _transportUnary,
      _replayUnary, _provenanceUnary, _localCertUnary, _sourceDense, _denseSeal,
        provenancePkg, localSemantic⟩ := carrier
  exact
    ⟨localSemantic, sourceMetricUnary, completionTargetUnary, denseImageUnary,
      isometryUnary, regularCauchyUnary, hausdorffBoundaryUnary, realSealUnary,
      provenancePkg⟩

theorem CompletionEmbeddingCarrier_source_density_reflection [AskSetup] [PackageSetup]
    {sourceMetric completionTarget denseImage isometry regularCauchy hausdorffBoundary
      realSeal transport replay provenance localCert denseRead isoRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionEmbeddingCarrier sourceMetric completionTarget denseImage isometry regularCauchy
        hausdorffBoundary realSeal transport replay provenance localCert bundle pkg →
      Cont regularCauchy denseImage denseRead →
        Cont denseRead isometry isoRead →
          Cont realSeal hausdorffBoundary endpointRead →
            PkgSig bundle endpointRead pkg →
              UnaryHistory sourceMetric ∧ UnaryHistory regularCauchy ∧
                UnaryHistory denseRead ∧ UnaryHistory isoRead ∧ UnaryHistory endpointRead ∧
                  Cont sourceMetric regularCauchy denseImage ∧
                    Cont regularCauchy denseImage denseRead ∧
                      Cont denseRead isometry isoRead ∧
                        Cont realSeal hausdorffBoundary endpointRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier regularDense denseIso realBoundary endpointPkg
  obtain ⟨sourceMetricUnary, _completionTargetUnary, denseImageUnary, isometryUnary,
    regularCauchyUnary, hausdorffBoundaryUnary, realSealUnary, _transportUnary,
      _replayUnary, _provenanceUnary, _localCertUnary, sourceDense, _denseSeal,
        provenancePkg, _localSemantic⟩ := carrier
  have denseReadUnary : UnaryHistory denseRead :=
    unary_cont_closed regularCauchyUnary denseImageUnary regularDense
  have isoReadUnary : UnaryHistory isoRead :=
    unary_cont_closed denseReadUnary isometryUnary denseIso
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed realSealUnary hausdorffBoundaryUnary realBoundary
  exact
    ⟨sourceMetricUnary, regularCauchyUnary, denseReadUnary, isoReadUnary,
      endpointReadUnary, sourceDense, regularDense, denseIso, realBoundary, provenancePkg,
      endpointPkg⟩

theorem CompletionEmbeddingCarrier_obligation_closure_package [AskSetup] [PackageSetup]
    {sourceMetric completionTarget denseImage isometry regularCauchy hausdorffBoundary
      realSeal transport replay provenance localCert denseRead isoRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionEmbeddingCarrier sourceMetric completionTarget denseImage isometry regularCauchy
        hausdorffBoundary realSeal transport replay provenance localCert bundle pkg ->
      Cont regularCauchy denseImage denseRead ->
        Cont denseRead isometry isoRead ->
          Cont realSeal hausdorffBoundary endpointRead ->
            PkgSig bundle endpointRead pkg ->
              SemanticNameCert
                    (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row sourceMetric ∨ hsame row regularCauchy ∨
                        hsame row denseImage ∨ hsame row isometry ∨ hsame row realSeal ∨
                          hsame row hausdorffBoundary ∨ hsame row denseRead ∨
                            hsame row isoRead ∨ hsame row endpointRead)
                    (fun row : BHist =>
                      hsame row endpointRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle endpointRead pkg)
                    hsame ∧
                  UnaryHistory denseRead ∧ UnaryHistory isoRead ∧
                    UnaryHistory endpointRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert
  intro carrier regularDense denseIso realBoundary endpointPkg
  obtain ⟨_sourceMetricUnary, _completionTargetUnary, denseImageUnary, isometryUnary,
    regularCauchyUnary, hausdorffBoundaryUnary, realSealUnary, _transportUnary,
      _replayUnary, _provenanceUnary, _localCertUnary, _sourceDense, _denseSeal,
        provenancePkg, _localSemantic⟩ := carrier
  have denseReadUnary : UnaryHistory denseRead :=
    unary_cont_closed regularCauchyUnary denseImageUnary regularDense
  have isoReadUnary : UnaryHistory isoRead :=
    unary_cont_closed denseReadUnary isometryUnary denseIso
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed realSealUnary hausdorffBoundaryUnary realBoundary
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceMetric ∨ hsame row regularCauchy ∨ hsame row denseImage ∨
              hsame row isometry ∨ hsame row realSeal ∨ hsame row hausdorffBoundary ∨
                hsame row denseRead ∨ hsame row isoRead ∨ hsame row endpointRead)
          (fun row : BHist =>
            hsame row endpointRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle endpointRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpointRead
        ⟨hsame_refl endpointRead, endpointReadUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg, endpointPkg⟩
  }
  exact ⟨cert, denseReadUnary, isoReadUnary, endpointReadUnary⟩

end BEDC.Derived.CompletionEmbeddingUp
