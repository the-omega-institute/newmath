import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.OtherMindsCommitmentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def OtherMindsCommitmentCarrier [AskSetup] [PackageSetup]
    (observer candidate locality evidence gap transports routes provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory observer ∧ UnaryHistory candidate ∧ UnaryHistory locality ∧
    UnaryHistory evidence ∧ UnaryHistory gap ∧ UnaryHistory transports ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory nameCert ∧
        Cont observer candidate locality ∧ Cont locality evidence routes ∧
          PkgSig bundle provenance pkg

theorem OtherMindsCommitmentCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {observer candidate locality evidence gap transports routes provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OtherMindsCommitmentCarrier observer candidate locality evidence gap transports routes
        provenance nameCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          OtherMindsCommitmentCarrier observer candidate locality evidence gap transports
            routes provenance nameCert bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          hsame row nameCert ∧ Cont observer candidate locality ∧
            Cont locality evidence routes)
        (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row nameCert)
        hsame ∧ Cont observer candidate locality ∧ Cont locality evidence routes ∧
          PkgSig bundle provenance pkg := by
  intro carrier
  have carrierWitness := carrier
  obtain ⟨_observerUnary, _candidateUnary, _localityUnary, _evidenceUnary, _gapUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, nameCertUnary, observerCandidateLocality,
    localityEvidenceRoutes, provenancePkg⟩ := carrier
  have sourceNameCert :
      (fun row : BHist =>
        OtherMindsCommitmentCarrier observer candidate locality evidence gap transports routes
          provenance nameCert bundle pkg ∧ hsame row nameCert) nameCert := by
    exact And.intro carrierWitness (hsame_refl nameCert)
  have core :
      NameCert
        (fun row : BHist =>
          OtherMindsCommitmentCarrier observer candidate locality evidence gap transports routes
            provenance nameCert bundle pkg ∧ hsame row nameCert)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro nameCert sourceNameCert
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same sourceRow
        have sameRowNameCert : hsame row nameCert := sourceRow.right
        have sameOtherNameCert : hsame other nameCert :=
          hsame_trans (hsame_symm same) sameRowNameCert
        exact And.intro sourceRow.left sameOtherNameCert
    }
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          OtherMindsCommitmentCarrier observer candidate locality evidence gap transports routes
            provenance nameCert bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          hsame row nameCert ∧ Cont observer candidate locality ∧
            Cont locality evidence routes)
        (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row nameCert)
        hsame := by
    exact {
      core := core
      pattern_sound := by
        intro row sourceRow
        exact ⟨sourceRow.right, observerCandidateLocality, localityEvidenceRoutes⟩
      ledger_sound := by
        intro row sourceRow
        exact And.intro provenancePkg sourceRow.right
    }
  exact ⟨cert, observerCandidateLocality, localityEvidenceRoutes, provenancePkg⟩

theorem OtherMindsCommitmentPublicEvidenceLedger [AskSetup] [PackageSetup]
    {observer candidate locality evidence gap transports routes provenance nameCert
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OtherMindsCommitmentCarrier observer candidate locality evidence gap transports routes
        provenance nameCert bundle pkg →
      Cont locality evidence publicRead →
        PkgSig bundle provenance pkg →
          UnaryHistory locality ∧
            UnaryHistory evidence ∧
              UnaryHistory publicRead ∧
                Cont locality evidence routes ∧
                  Cont locality evidence publicRead ∧
                    PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg AskSetup PackageSetup
  intro carrier publicCont provenancePkg
  rcases carrier with
    ⟨_observerUnary, _candidateUnary, localityUnary, evidenceUnary, _gapUnary,
      _transportsUnary, _routesUnary, _provenanceUnary, _nameCertUnary,
      _observerCandidateLocality, localityEvidenceRoutes, _carrierPkg⟩
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed localityUnary evidenceUnary publicCont
  exact
    ⟨localityUnary, evidenceUnary, publicUnary, localityEvidenceRoutes, publicCont,
      provenancePkg⟩

theorem OtherMindsCommitmentLocalityCellSoundness [AskSetup] [PackageSetup]
    {observer candidate locality evidence gap transports routes provenance nameCert publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OtherMindsCommitmentCarrier observer candidate locality evidence gap transports routes
        provenance nameCert bundle pkg →
      Cont locality evidence publicRead →
        PkgSig bundle provenance pkg →
          UnaryHistory observer ∧ UnaryHistory candidate ∧ UnaryHistory locality ∧
            UnaryHistory evidence ∧ UnaryHistory publicRead ∧
              Cont observer candidate locality ∧ Cont locality evidence publicRead ∧
                PkgSig bundle provenance pkg ∧ hsame locality locality := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame UnaryHistory
  intro carrier publicCont provenancePkg
  rcases carrier with
    ⟨observerUnary, candidateUnary, localityUnary, evidenceUnary, _gapUnary,
      _transportsUnary, _routesUnary, _provenanceUnary, _nameCertUnary,
      observerCandidateLocality, _localityEvidenceRoutes, _carrierPkg⟩
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed localityUnary evidenceUnary publicCont
  exact
    ⟨observerUnary, candidateUnary, localityUnary, evidenceUnary, publicUnary,
      observerCandidateLocality, publicCont, provenancePkg, hsame_refl locality⟩

theorem OtherMindsCommitmentBehaviouralEvidenceCompatibility [AskSetup] [PackageSetup]
    {observer candidate locality evidence gap transports routes provenance nameCert
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OtherMindsCommitmentCarrier observer candidate locality evidence gap transports routes
        provenance nameCert bundle pkg →
      Cont locality evidence publicRead →
        PkgSig bundle provenance pkg →
          UnaryHistory observer ∧ UnaryHistory candidate ∧ UnaryHistory locality ∧
            UnaryHistory evidence ∧ UnaryHistory publicRead ∧
              Cont observer candidate locality ∧ Cont locality evidence routes ∧
                Cont locality evidence publicRead ∧ PkgSig bundle provenance pkg ∧
                  hsame evidence evidence := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame UnaryHistory
  intro carrier publicCont provenancePkg
  rcases carrier with
    ⟨observerUnary, candidateUnary, localityUnary, evidenceUnary, _gapUnary,
      _transportsUnary, _routesUnary, _provenanceUnary, _nameCertUnary,
      observerCandidateLocality, localityEvidenceRoutes, _carrierPkg⟩
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed localityUnary evidenceUnary publicCont
  exact
    ⟨observerUnary, candidateUnary, localityUnary, evidenceUnary, publicUnary,
      observerCandidateLocality, localityEvidenceRoutes, publicCont, provenancePkg,
      hsame_refl evidence⟩

theorem OtherMindsCommitmentNonEscapeBoundary [AskSetup] [PackageSetup]
    {observer candidate locality evidence gap transports routes provenance nameCert
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OtherMindsCommitmentCarrier observer candidate locality evidence gap transports routes
        provenance nameCert bundle pkg →
      Cont locality evidence publicRead →
        PkgSig bundle provenance pkg →
          UnaryHistory observer ∧ UnaryHistory candidate ∧ UnaryHistory locality ∧
            UnaryHistory evidence ∧ UnaryHistory gap ∧ UnaryHistory transports ∧
              UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory nameCert ∧
                UnaryHistory publicRead ∧ Cont observer candidate locality ∧
                  Cont locality evidence routes ∧ Cont locality evidence publicRead ∧
                    PkgSig bundle provenance pkg ∧ hsame nameCert nameCert := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame UnaryHistory
  intro carrier publicCont provenancePkg
  rcases carrier with
    ⟨observerUnary, candidateUnary, localityUnary, evidenceUnary, gapUnary,
      transportsUnary, routesUnary, provenanceUnary, nameCertUnary,
      observerCandidateLocality, localityEvidenceRoutes, _carrierPkg⟩
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed localityUnary evidenceUnary publicCont
  exact
    ⟨observerUnary, candidateUnary, localityUnary, evidenceUnary, gapUnary,
      transportsUnary, routesUnary, provenanceUnary, nameCertUnary, publicUnary,
      observerCandidateLocality, localityEvidenceRoutes, publicCont, provenancePkg,
      hsame_refl nameCert⟩

theorem OtherMindsCommitmentObligationClosurePackage [AskSetup] [PackageSetup]
    {observer candidate locality evidence gap transports routes provenance nameCert publicRead
      closureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OtherMindsCommitmentCarrier observer candidate locality evidence gap transports routes
        provenance nameCert bundle pkg →
      Cont locality evidence publicRead →
        Cont provenance nameCert closureRead →
          PkgSig bundle provenance pkg →
            SemanticNameCert
              (fun row : BHist =>
                OtherMindsCommitmentCarrier observer candidate locality evidence gap transports
                  routes provenance nameCert bundle pkg ∧ hsame row nameCert)
              (fun row : BHist =>
                hsame row nameCert ∧ Cont observer candidate locality ∧
                  Cont locality evidence routes)
              (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row nameCert)
              hsame ∧ UnaryHistory publicRead ∧ UnaryHistory closureRead ∧
                Cont observer candidate locality ∧ Cont locality evidence publicRead ∧
                  Cont provenance nameCert closureRead ∧ PkgSig bundle provenance pkg ∧
                    hsame nameCert nameCert := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier publicCont closureCont provenancePkg
  have obligations :=
    OtherMindsCommitmentCarrier_namecert_obligations
      (observer := observer) (candidate := candidate) (locality := locality)
      (evidence := evidence) (gap := gap) (transports := transports)
      (routes := routes) (provenance := provenance) (nameCert := nameCert)
      (bundle := bundle) (pkg := pkg) carrier
  rcases obligations with
    ⟨cert, observerCandidateLocality, _localityEvidenceRoutes, _carrierPkg⟩
  rcases carrier with
    ⟨_observerUnary, _candidateUnary, localityUnary, evidenceUnary, _gapUnary,
      _transportsUnary, _routesUnary, provenanceUnary, nameCertUnary,
      _observerCandidateLocality, _localityEvidenceRoutes, _carrierPkg'⟩
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed localityUnary evidenceUnary publicCont
  have closureUnary : UnaryHistory closureRead :=
    unary_cont_closed provenanceUnary nameCertUnary closureCont
  exact
    ⟨cert, publicUnary, closureUnary, observerCandidateLocality, publicCont,
      closureCont, provenancePkg, hsame_refl nameCert⟩

end BEDC.Derived.OtherMindsCommitmentUp
