import BEDC.Derived.MetricCompletionUp.NameCertObligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricCompletionUp.ScopedDependencyPackage

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.MetricCompletionUp.NameCertObligations

theorem MetricCompletion_scoped_dependency_package [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      selectedBranch branchRead readbackRead separatedRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      (hsame selectedBranch filterBranch ∨ hsame selectedBranch netBranch) →
        Cont source selectedBranch branchRead →
          Cont branchRead readback readbackRead →
            Cont readbackRead separated separatedRead →
              Cont separatedRead replay uniformRead →
                PkgSig bundle uniformRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row source ∨ hsame row selectedBranch ∨
                          hsame row branchRead ∨ hsame row readbackRead ∨
                            hsame row separatedRead ∨ hsame row uniformRead)
                      (fun row : BHist =>
                        hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
                      hsame ∧
                    UnaryHistory source ∧ UnaryHistory selectedBranch ∧
                      UnaryHistory branchRead ∧ UnaryHistory readbackRead ∧
                        UnaryHistory separatedRead ∧ UnaryHistory uniformRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro carrier branchChoice sourceBranch branchReadback readbackSeparated separatedUniform
    uniformPkg
  obtain ⟨sourceUnary, filterUnary, netUnary, readbackUnary, separatedUnary,
    _transportUnary, replayUnary, _provenanceUnary, _localCertUnary, _carrierReplayRoute,
    _transportSame, _provenancePkg, _localCertPkg⟩ := carrier
  have selectedUnary : UnaryHistory selectedBranch := by
    cases branchChoice with
    | inl sameFilter =>
        exact unary_transport_symm filterUnary sameFilter
    | inr sameNet =>
        exact unary_transport_symm netUnary sameNet
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed sourceUnary selectedUnary sourceBranch
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed branchReadUnary readbackUnary branchReadback
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed readbackReadUnary separatedUnary readbackSeparated
  have uniformReadUnary : UnaryHistory uniformRead :=
    unary_cont_closed separatedReadUnary replayUnary separatedUniform
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row selectedBranch ∨ hsame row branchRead ∨
              hsame row readbackRead ∨ hsame row separatedRead ∨ hsame row uniformRead)
          (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro uniformRead
          ⟨hsame_refl uniformRead, uniformReadUnary⟩
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
        exact ⟨sourceRow.left, uniformPkg⟩
    }
  exact
    ⟨cert, sourceUnary, selectedUnary, branchReadUnary, readbackReadUnary,
      separatedReadUnary, uniformReadUnary⟩

end BEDC.Derived.MetricCompletionUp.ScopedDependencyPackage
