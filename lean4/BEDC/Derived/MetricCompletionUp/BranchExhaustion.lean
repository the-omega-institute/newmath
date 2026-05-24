import BEDC.Derived.MetricCompletionUp.NameCertObligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricCompletionUp.BranchExhaustion

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.MetricCompletionUp.NameCertObligations

theorem MetricCompletion_filter_net_branch_exhaustion [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      selectedBranch branchRead exportRead ledgerExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      (hsame selectedBranch filterBranch ∨ hsame selectedBranch netBranch) →
        Cont source selectedBranch branchRead →
          Cont branchRead readback exportRead →
            Cont readback separated replay →
              Cont replay localCert ledgerExport →
                PkgSig bundle exportRead pkg →
                  PkgSig bundle ledgerExport pkg →
                    UnaryHistory selectedBranch ∧ UnaryHistory branchRead ∧
                      UnaryHistory exportRead ∧ UnaryHistory ledgerExport ∧
                        Cont source selectedBranch branchRead ∧
                          Cont branchRead readback exportRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle exportRead pkg ∧
                              PkgSig bundle ledgerExport pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle PkgSig UnaryHistory
  intro carrier branchChoice branchRoute exportRoute replayRoute ledgerRoute exportPkg ledgerPkg
  obtain ⟨sourceUnary, filterUnary, netUnary, readbackUnary, separatedUnary,
    _transportUnary, _replayUnary, _provenanceUnary, localCertUnary, _carrierReplayRoute,
    _transportSame, provenancePkg, _localCertPkg⟩ := carrier
  have selectedUnary : UnaryHistory selectedBranch := by
    cases branchChoice with
    | inl sameFilter =>
        exact unary_transport filterUnary (hsame_symm sameFilter)
    | inr sameNet =>
        exact unary_transport netUnary (hsame_symm sameNet)
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed sourceUnary selectedUnary branchRoute
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed branchReadUnary readbackUnary exportRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed readbackUnary separatedUnary replayRoute
  have ledgerUnary : UnaryHistory ledgerExport :=
    unary_cont_closed replayUnary localCertUnary ledgerRoute
  exact
    ⟨selectedUnary, branchReadUnary, exportUnary, ledgerUnary, branchRoute, exportRoute,
      provenancePkg, exportPkg, ledgerPkg⟩

end BEDC.Derived.MetricCompletionUp.BranchExhaustion
