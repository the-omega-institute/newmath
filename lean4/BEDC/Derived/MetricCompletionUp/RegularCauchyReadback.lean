import BEDC.Derived.MetricCompletionUp.NameCertObligations

namespace BEDC.Derived.MetricCompletionUp.RegularCauchyReadback

open BEDC.Derived.MetricCompletionUp.NameCertObligations
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricCompletion_regular_cauchy_readback [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      selectedBranch branchRead toleranceRead sealedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      (hsame selectedBranch filterBranch ∨ hsame selectedBranch netBranch) →
      Cont source selectedBranch branchRead → Cont branchRead readback toleranceRead →
      Cont toleranceRead separated sealedRead → PkgSig bundle sealedRead pkg →
      SemanticNameCert
          (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row selectedBranch ∨ hsame row branchRead ∨
              hsame row toleranceRead ∨ hsame row readback ∨ hsame row separated ∨
                hsame row sealedRead)
          (fun row : BHist => hsame row sealedRead ∧ PkgSig bundle sealedRead pkg)
          hsame ∧
        UnaryHistory source ∧ UnaryHistory selectedBranch ∧ UnaryHistory branchRead ∧
          UnaryHistory toleranceRead ∧ UnaryHistory sealedRead ∧
            Cont source selectedBranch branchRead ∧ Cont branchRead readback toleranceRead ∧
              Cont toleranceRead separated sealedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier selectedRoute sourceBranch branchReadback toleranceSeparated sealedPkg
  obtain ⟨sourceUnary, filterUnary, netUnary, readbackUnary, separatedUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _localCertUnary, _replayRoute, _transportSame,
    _provenancePkg, _localCertPkg⟩ := carrier
  have selectedUnary : UnaryHistory selectedBranch := by
    cases selectedRoute with
    | inl selectedFilter =>
        exact unary_transport filterUnary (hsame_symm selectedFilter)
    | inr selectedNet =>
        exact unary_transport netUnary (hsame_symm selectedNet)
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed sourceUnary selectedUnary sourceBranch
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed branchReadUnary readbackUnary branchReadback
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed toleranceUnary separatedUnary toleranceSeparated
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row selectedBranch ∨ hsame row branchRead ∨
              hsame row toleranceRead ∨ hsame row readback ∨ hsame row separated ∨
                hsame row sealedRead)
          (fun row : BHist => hsame row sealedRead ∧ PkgSig bundle sealedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealedRead (And.intro (hsame_refl sealedRead) sealedUnary)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact And.intro sourceRow.left sealedPkg
  }
  exact
    ⟨cert, sourceUnary, selectedUnary, branchReadUnary, toleranceUnary, sealedUnary,
      sourceBranch, branchReadback, toleranceSeparated⟩

end BEDC.Derived.MetricCompletionUp.RegularCauchyReadback
