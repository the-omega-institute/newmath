import BEDC.Derived.MetricCompletionUp.NameCertObligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricCompletionUp.RootObligations

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.MetricCompletionUp.NameCertObligations

theorem MetricCompletion_root_obligation_carrier [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      selectedBranch branchRead finiteReadback separatedRead rootEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg ->
      (hsame selectedBranch filterBranch ∨ hsame selectedBranch netBranch) ->
        Cont source selectedBranch branchRead ->
          Cont branchRead readback finiteReadback ->
            Cont finiteReadback separated separatedRead ->
              Cont separatedRead replay rootEndpoint ->
                PkgSig bundle rootEndpoint pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row rootEndpoint ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row source ∨ hsame row selectedBranch ∨ hsame row branchRead ∨
                          hsame row finiteReadback ∨ hsame row separatedRead ∨
                            hsame row rootEndpoint)
                      (fun row : BHist =>
                        hsame row rootEndpoint ∧ PkgSig bundle rootEndpoint pkg)
                      hsame ∧
                    UnaryHistory source ∧ UnaryHistory selectedBranch ∧
                      UnaryHistory branchRead ∧ UnaryHistory finiteReadback ∧
                        UnaryHistory separatedRead ∧ UnaryHistory rootEndpoint := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier branchChoice branchRoute finiteRoute separatedRoute rootRoute rootPkg
  obtain ⟨sourceUnary, filterUnary, netUnary, readbackUnary, separatedUnary,
    _transportUnary, replayUnary, _provenanceUnary, _localCertUnary, _replayRoute,
    _transportSame, _provenancePkg, _localCertPkg⟩ := carrier
  have selectedUnary : UnaryHistory selectedBranch := by
    cases branchChoice with
    | inl sameFilter =>
        exact unary_transport filterUnary (hsame_symm sameFilter)
    | inr sameNet =>
        exact unary_transport netUnary (hsame_symm sameNet)
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed sourceUnary selectedUnary branchRoute
  have finiteReadbackUnary : UnaryHistory finiteReadback :=
    unary_cont_closed branchReadUnary readbackUnary finiteRoute
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed finiteReadbackUnary separatedUnary separatedRoute
  have rootEndpointUnary : UnaryHistory rootEndpoint :=
    unary_cont_closed separatedReadUnary replayUnary rootRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootEndpoint ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row selectedBranch ∨ hsame row branchRead ∨
              hsame row finiteReadback ∨ hsame row separatedRead ∨ hsame row rootEndpoint)
          (fun row : BHist => hsame row rootEndpoint ∧ PkgSig bundle rootEndpoint pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro rootEndpoint
          ⟨hsame_refl rootEndpoint, rootEndpointUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, rootPkg⟩
    }
  exact
    ⟨cert, sourceUnary, selectedUnary, branchReadUnary, finiteReadbackUnary,
      separatedReadUnary, rootEndpointUnary⟩

theorem MetricCompletion_root_obligation_classifier [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      selectedBranch leftRead rightRead classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg ->
      (hsame selectedBranch filterBranch ∨ hsame selectedBranch netBranch) ->
        Cont source selectedBranch leftRead ->
          Cont leftRead separated rightRead ->
            hsame rightRead classifierRead ->
              PkgSig bundle classifierRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row source ∨ hsame row selectedBranch ∨ hsame row leftRead ∨
                        hsame row rightRead ∨ hsame row classifierRead)
                    (fun row : BHist =>
                      hsame row classifierRead ∧ PkgSig bundle classifierRead pkg)
                    hsame ∧
                  UnaryHistory selectedBranch ∧ UnaryHistory leftRead ∧
                    UnaryHistory rightRead ∧ UnaryHistory classifierRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier branchChoice branchRoute rightRoute sameClassifier classifierPkg
  obtain ⟨sourceUnary, filterUnary, netUnary, _readbackUnary, separatedUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localCertUnary, _replayRoute,
    _transportSame, _provenancePkg, _localCertPkg⟩ := carrier
  have selectedUnary : UnaryHistory selectedBranch := by
    cases branchChoice with
    | inl sameFilter =>
        exact unary_transport filterUnary (hsame_symm sameFilter)
    | inr sameNet =>
        exact unary_transport netUnary (hsame_symm sameNet)
  have leftReadUnary : UnaryHistory leftRead :=
    unary_cont_closed sourceUnary selectedUnary branchRoute
  have rightReadUnary : UnaryHistory rightRead :=
    unary_cont_closed leftReadUnary separatedUnary rightRoute
  have classifierReadUnary : UnaryHistory classifierRead :=
    unary_transport rightReadUnary sameClassifier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row selectedBranch ∨ hsame row leftRead ∨
              hsame row rightRead ∨ hsame row classifierRead)
          (fun row : BHist => hsame row classifierRead ∧ PkgSig bundle classifierRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro classifierRead
          ⟨hsame_refl classifierRead, classifierReadUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, classifierPkg⟩
    }
  exact ⟨cert, selectedUnary, leftReadUnary, rightReadUnary, classifierReadUnary⟩

end BEDC.Derived.MetricCompletionUp.RootObligations
