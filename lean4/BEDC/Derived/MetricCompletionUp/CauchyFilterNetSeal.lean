import BEDC.Derived.MetricCompletionUp.NameCertObligations

namespace BEDC.Derived.MetricCompletionUp.CauchyFilterNetSeal

open BEDC.Derived.MetricCompletionUp.NameCertObligations
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricCompletion_cauchy_filter_net_seal [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      filterSeal netSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      Cont filterBranch readback filterSeal →
        Cont netBranch readback netSeal →
          PkgSig bundle provenance pkg →
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row filterSeal ∨ hsame row netSeal) ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row filterBranch ∨ hsame row netBranch ∨ hsame row readback ∨
                    hsame row filterSeal ∨ hsame row netSeal)
                (fun row : BHist =>
                  (hsame row filterSeal ∨ hsame row netSeal) ∧
                    PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory filterSeal ∧ UnaryHistory netSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig SemanticNameCert hsame Cont
  intro carrier filterRoute netRoute provenancePkg
  obtain ⟨_sourceUnary, filterUnary, netUnary, readbackUnary, _separatedUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localCertUnary, _replayRoute,
    _transportSame, _carrierProvenancePkg, _localCertPkg⟩ := carrier
  have filterSealUnary : UnaryHistory filterSeal :=
    unary_cont_closed filterUnary readbackUnary filterRoute
  have netSealUnary : UnaryHistory netSeal :=
    unary_cont_closed netUnary readbackUnary netRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row filterSeal ∨ hsame row netSeal) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row filterBranch ∨ hsame row netBranch ∨ hsame row readback ∨
              hsame row filterSeal ∨ hsame row netSeal)
          (fun row : BHist =>
            (hsame row filterSeal ∨ hsame row netSeal) ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro filterSeal
          (And.intro (Or.inl (hsame_refl filterSeal)) filterSealUnary)
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
          | inl sameFilterSeal =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameFilterSeal)
          | inr sameNetSeal =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameNetSeal)
        · exact unary_transport sourceRow.right sameRows
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow.left with
      | inl sameFilterSeal =>
          exact Or.inr (Or.inr (Or.inr (Or.inl sameFilterSeal)))
      | inr sameNetSeal =>
          exact Or.inr (Or.inr (Or.inr (Or.inr sameNetSeal)))
    ledger_sound := by
      intro _row sourceRow
      exact And.intro sourceRow.left provenancePkg
  }
  exact ⟨cert, filterSealUnary, netSealUnary⟩

end BEDC.Derived.MetricCompletionUp.CauchyFilterNetSeal
