import BEDC.Derived.MetricCompletionUp.NameCertObligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricCompletionUp.BranchDeterminacy

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.MetricCompletionUp.NameCertObligations

theorem MetricCompletion_filter_net_branch_determinacy [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      filterRead netRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      Cont source filterBranch filterRead →
        Cont source netBranch netRead →
          Cont readback separated replay →
            Cont replay localCert exportRead →
              PkgSig bundle exportRead pkg →
                SemanticNameCert
                    (fun row : BHist => (hsame row filterRead ∨ hsame row netRead) ∧
                      UnaryHistory row)
                    (fun row : BHist => hsame row filterRead ∨ hsame row netRead)
                    (fun row : BHist => (hsame row filterRead ∨ hsame row netRead) ∧
                      PkgSig bundle exportRead pkg)
                    hsame ∧
                  UnaryHistory filterRead ∧ UnaryHistory netRead ∧ UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier filterRoute netRoute replayRoute exportRoute exportPkg
  obtain ⟨sourceUnary, filterUnary, netUnary, readbackUnary, separatedUnary,
    _transportUnary, _replayUnaryCarrier, _provenanceUnary, localCertUnary,
    _carrierReplayRoute, _transportSame, _provenancePkg, _localCertPkg⟩ := carrier
  have filterReadUnary : UnaryHistory filterRead :=
    unary_cont_closed sourceUnary filterUnary filterRoute
  have netReadUnary : UnaryHistory netRead :=
    unary_cont_closed sourceUnary netUnary netRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed readbackUnary separatedUnary replayRoute
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed replayUnary localCertUnary exportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => (hsame row filterRead ∨ hsame row netRead) ∧ UnaryHistory row)
          (fun row : BHist => hsame row filterRead ∨ hsame row netRead)
          (fun row : BHist =>
            (hsame row filterRead ∨ hsame row netRead) ∧ PkgSig bundle exportRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro filterRead ⟨Or.inl (hsame_refl filterRead), filterReadUnary⟩
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
        exact sourceRow.left
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, exportPkg⟩
    }
  exact ⟨cert, filterReadUnary, netReadUnary, exportUnary⟩

end BEDC.Derived.MetricCompletionUp.BranchDeterminacy
