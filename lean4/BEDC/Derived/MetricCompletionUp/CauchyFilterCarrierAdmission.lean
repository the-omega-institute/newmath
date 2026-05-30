import BEDC.Derived.MetricCompletionUp.ScopedReadbackScope
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricCompletionUp.CauchyFilterCarrierAdmission

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.MetricCompletionUp.NameCertObligations
open BEDC.Derived.MetricCompletionUp.ScopedReadbackScope

theorem MetricCompletion_cauchyfilter_carrier_admission [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      filterRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionScopedReadbackScope source filterBranch netBranch readback separated transport
        replay provenance localCert filterBranch bundle pkg →
      Cont filterBranch readback filterRead →
        PkgSig bundle filterRead pkg →
          UnaryHistory source ∧ UnaryHistory filterBranch ∧ UnaryHistory readback ∧
            UnaryHistory separated ∧ UnaryHistory filterRead ∧
              Cont filterBranch readback filterRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle filterRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle PkgSig hsame
  intro scope filterRoute filterPkg
  obtain ⟨carrier, _scopeBranch, _branchUnary⟩ := scope
  obtain ⟨sourceUnary, filterUnary, _netUnary, readbackUnary, separatedUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localCertUnary, _replayRoute,
    _transportSame, provenancePkg, _localCertPkg⟩ := carrier
  have filterReadUnary : UnaryHistory filterRead :=
    unary_cont_closed filterUnary readbackUnary filterRoute
  exact
    ⟨sourceUnary, filterUnary, readbackUnary, separatedUnary, filterReadUnary, filterRoute,
      provenancePkg, filterPkg⟩

end BEDC.Derived.MetricCompletionUp.CauchyFilterCarrierAdmission
