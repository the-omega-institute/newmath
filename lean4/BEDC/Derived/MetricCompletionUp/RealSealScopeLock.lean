import BEDC.Derived.MetricCompletionUp.NameCertObligations

namespace BEDC.Derived.MetricCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.MetricCompletionUp.NameCertObligations

theorem MetricCompletion_real_seal_scope_lock [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      selectedBranch branchRead finiteReadback separatedRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg ->
      (hsame selectedBranch filterBranch ∨ hsame selectedBranch netBranch) ->
        Cont source selectedBranch branchRead ->
          Cont branchRead readback finiteReadback ->
            Cont finiteReadback separated separatedRead ->
              Cont separatedRead localCert handoffRead ->
                PkgSig bundle handoffRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row selectedBranch ∨ hsame row finiteReadback ∨
                          hsame row separatedRead ∨ hsame row handoffRead)
                      (fun row : BHist =>
                        hsame row handoffRead ∧ PkgSig bundle handoffRead pkg)
                      hsame ∧
                    UnaryHistory selectedBranch ∧ UnaryHistory finiteReadback ∧
                      UnaryHistory separatedRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier selectedChoice sourceBranch branchReadback finiteSeparated separatedHandoff
    handoffPkg
  obtain ⟨sourceUnary, filterUnary, netUnary, readbackUnary, separatedUnary,
    _transportUnary, _replayUnary, _provenanceUnary, localCertUnary, _replayRoute,
    _transportSame, _provenancePkg, _localCertPkg⟩ := carrier
  have selectedUnary : UnaryHistory selectedBranch := by
    cases selectedChoice with
    | inl sameFilter =>
        exact unary_transport_symm filterUnary sameFilter
    | inr sameNet =>
        exact unary_transport_symm netUnary sameNet
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed sourceUnary selectedUnary sourceBranch
  have finiteReadbackUnary : UnaryHistory finiteReadback :=
    unary_cont_closed branchReadUnary readbackUnary branchReadback
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed finiteReadbackUnary separatedUnary finiteSeparated
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed separatedReadUnary localCertUnary separatedHandoff
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row selectedBranch ∨ hsame row finiteReadback ∨
              hsame row separatedRead ∨ hsame row handoffRead)
          (fun row : BHist => hsame row handoffRead ∧ PkgSig bundle handoffRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro handoffRead ⟨hsame_refl handoffRead,
          handoffUnary⟩
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
        exact ⟨sourceRow.left, handoffPkg⟩
    }
  exact ⟨cert, selectedUnary, finiteReadbackUnary, separatedReadUnary, handoffUnary⟩

end BEDC.Derived.MetricCompletionUp
