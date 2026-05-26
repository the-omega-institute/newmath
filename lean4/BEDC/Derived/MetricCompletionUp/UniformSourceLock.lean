import BEDC.Derived.MetricCompletionUp.NameCertObligations

namespace BEDC.Derived.MetricCompletionUp.UniformSourceLock

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.MetricCompletionUp.NameCertObligations

theorem MetricCompletion_uniform_source_lock [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      selectedBranch branchRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      (hsame selectedBranch filterBranch ∨ hsame selectedBranch netBranch) →
        Cont source selectedBranch branchRead →
          Cont branchRead replay uniformRead →
            PkgSig bundle uniformRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row source ∨ hsame row selectedBranch ∨ hsame row branchRead ∨
                      hsame row uniformRead)
                  (fun row : BHist =>
                    hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
                  hsame ∧
                UnaryHistory source ∧ UnaryHistory selectedBranch ∧ UnaryHistory branchRead ∧
                  UnaryHistory uniformRead ∧ Cont source selectedBranch branchRead ∧
                    Cont branchRead replay uniformRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier selectedChoice sourceBranch branchUniform uniformPkg
  obtain ⟨sourceUnary, filterUnary, netUnary, _readbackUnary, _separatedUnary,
    _transportUnary, replayUnary, _provenanceUnary, _localCertUnary, _replayRoute,
    _transportSame, _provenancePkg, _localCertPkg⟩ := carrier
  have selectedUnary : UnaryHistory selectedBranch := by
    cases selectedChoice with
    | inl sameFilter =>
        exact unary_transport_symm filterUnary sameFilter
    | inr sameNet =>
        exact unary_transport_symm netUnary sameNet
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed sourceUnary selectedUnary sourceBranch
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed branchReadUnary replayUnary branchUniform
  have sourceUniform :
      (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row) uniformRead := by
    exact ⟨hsame_refl uniformRead, uniformUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row selectedBranch ∨ hsame row branchRead ∨
              hsame row uniformRead)
          (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro uniformRead sourceUniform
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
            ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
              unary_transport sourceRow.right sameRows⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr sourceRow.left))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, uniformPkg⟩
    }
  exact
    ⟨cert, sourceUnary, selectedUnary, branchReadUnary, uniformUnary, sourceBranch,
      branchUniform⟩

end BEDC.Derived.MetricCompletionUp.UniformSourceLock
