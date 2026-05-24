import BEDC.Derived.MetricCompletionUp.NameCertObligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricCompletionUp.BranchCoverage

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.MetricCompletionUp.NameCertObligations

theorem MetricCompletion_branch_coverage [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance
      localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            (hsame row filterBranch ∨ hsame row netBranch) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row filterBranch ∨ hsame row netBranch ∨
              hsame row readback)
          (fun row : BHist =>
            (hsame row filterBranch ∨ hsame row netBranch) ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory filterBranch ∧ UnaryHistory netBranch ∧
          PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier
  obtain ⟨_sourceUnary, filterUnary, netUnary, _readbackUnary, _separatedUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localCertUnary, _replayRoute,
    _transportSame, provenancePkg, _localCertPkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row filterBranch ∨ hsame row netBranch) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row filterBranch ∨ hsame row netBranch ∨
              hsame row readback)
          (fun row : BHist =>
            (hsame row filterBranch ∨ hsame row netBranch) ∧ PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro filterBranch ⟨Or.inl (hsame_refl filterBranch), filterUnary⟩
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
          constructor
          · cases sourceRow.left with
            | inl sameFilter =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameFilter)
            | inr sameNet =>
                exact Or.inr (hsame_trans (hsame_symm sameRows) sameNet)
          · exact unary_transport sourceRow.right sameRows
      }
      pattern_sound := by
        intro _row sourceRow
        cases sourceRow.left with
        | inl sameFilter =>
            exact Or.inr (Or.inl sameFilter)
        | inr sameNet =>
            exact Or.inr (Or.inr (Or.inl sameNet))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, provenancePkg⟩
    }
  exact ⟨cert, filterUnary, netUnary, provenancePkg⟩

end BEDC.Derived.MetricCompletionUp.BranchCoverage
