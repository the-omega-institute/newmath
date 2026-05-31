import BEDC.Derived.MetricCompletionUp.NameCertObligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricCompletionUp.RootObligationCarrierWitness

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.MetricCompletionUp.NameCertObligations

theorem MetricCompletion_root_obligation_carrier_witness [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      selectedBranch branchRead witnessRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      (hsame selectedBranch filterBranch ∨ hsame selectedBranch netBranch) →
        Cont source selectedBranch branchRead →
          Cont branchRead readback witnessRead →
            PkgSig bundle witnessRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row witnessRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row source ∨ hsame row selectedBranch ∨ hsame row branchRead ∨
                      hsame row readback ∨ hsame row witnessRead)
                  (fun row : BHist => hsame row witnessRead ∧ PkgSig bundle witnessRead pkg)
                  hsame ∧
                UnaryHistory source ∧ UnaryHistory selectedBranch ∧ UnaryHistory branchRead ∧
                  UnaryHistory witnessRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier branchChoice branchRoute witnessRoute witnessPkg
  obtain ⟨sourceUnary, filterUnary, netUnary, readbackUnary, _separatedUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localCertUnary, _replayRoute,
    _transportSame, _provenancePkg, _localCertPkg⟩ := carrier
  have selectedUnary : UnaryHistory selectedBranch := by
    cases branchChoice with
    | inl sameFilter =>
        exact unary_transport filterUnary (hsame_symm sameFilter)
    | inr sameNet =>
        exact unary_transport netUnary (hsame_symm sameNet)
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed sourceUnary selectedUnary branchRoute
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed branchReadUnary readbackUnary witnessRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row witnessRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row selectedBranch ∨ hsame row branchRead ∨
              hsame row readback ∨ hsame row witnessRead)
          (fun row : BHist => hsame row witnessRead ∧ PkgSig bundle witnessRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro witnessRead ⟨hsame_refl witnessRead, witnessUnary⟩
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
          · exact hsame_trans (hsame_symm sameRows) sourceRow.left
          · exact unary_transport sourceRow.right sameRows
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, witnessPkg⟩
    }
  exact ⟨cert, sourceUnary, selectedUnary, branchReadUnary, witnessUnary⟩

end BEDC.Derived.MetricCompletionUp.RootObligationCarrierWitness
