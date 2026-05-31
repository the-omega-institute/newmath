import BEDC.Derived.MetricCompletionUp.NameCertObligations

namespace BEDC.Derived.MetricCompletionUp.CauchyEvidenceHandoff

open BEDC.Derived.MetricCompletionUp.NameCertObligations
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricCompletion_cauchy_evidence_handoff [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance
      localCert selected : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      (hsame selected filterBranch ∨ hsame selected netBranch) →
        Cont source selected readback →
          Cont readback separated replay →
            hsame replay provenance →
              PkgSig bundle provenance pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row replay ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row source ∨ hsame row selected ∨ hsame row readback ∨
                        hsame row separated ∨ hsame row replay)
                    (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
                    hsame ∧
                  UnaryHistory source ∧ UnaryHistory selected ∧ UnaryHistory readback ∧
                    UnaryHistory replay := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig SemanticNameCert hsame Cont
  intro carrier selectedBranch _sourceSelected readbackSeparated replayProvenance provenancePkg
  obtain ⟨sourceUnary, filterUnary, netUnary, readbackUnary, separatedUnary, _transportUnary,
    _replayUnaryCarrier, _provenanceUnary, _localCertUnary, _carrierReplayRoute,
    _transportSame, _carrierProvenancePkg, _localCertPkg⟩ := carrier
  have selectedUnary : UnaryHistory selected := by
    cases selectedBranch with
    | inl selectedFilter =>
        exact unary_transport filterUnary (hsame_symm selectedFilter)
    | inr selectedNet =>
        exact unary_transport netUnary (hsame_symm selectedNet)
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed readbackUnary separatedUnary readbackSeparated
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replay ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row selected ∨ hsame row readback ∨
              hsame row separated ∨ hsame row replay)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro replay (And.intro (hsame_refl replay) replayUnary)
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
        intro _row _other sameRows sourceRow
        exact
          And.intro (hsame_trans (hsame_symm sameRows) sourceRow.left)
            (unary_transport sourceRow.right sameRows)
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
    ledger_sound := by
      intro _row sourceRow
      exact And.intro (hsame_trans sourceRow.left replayProvenance) provenancePkg
  }
  exact ⟨cert, sourceUnary, selectedUnary, readbackUnary, replayUnary⟩

end BEDC.Derived.MetricCompletionUp.CauchyEvidenceHandoff
