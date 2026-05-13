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

end BEDC.Derived.OtherMindsCommitmentUp
