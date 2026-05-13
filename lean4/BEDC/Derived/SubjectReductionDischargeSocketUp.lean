import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SubjectReductionDischargeSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SubjectReductionDischargeSocketPacket [AskSetup] [PackageSetup]
    (beta appArg lamDomain piDomain transport routes ledger name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory beta ∧ UnaryHistory appArg ∧ UnaryHistory lamDomain ∧
    UnaryHistory piDomain ∧ UnaryHistory transport ∧ UnaryHistory routes ∧
      UnaryHistory ledger ∧ UnaryHistory name ∧ Cont beta appArg transport ∧
        Cont lamDomain piDomain routes ∧ Cont transport routes ledger ∧
          Cont ledger name beta ∧ PkgSig bundle name pkg

theorem SubjectReductionDischargeSocketPacket_nonescape [AskSetup] [PackageSetup]
    {beta appArg lamDomain piDomain transport routes ledger name consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubjectReductionDischargeSocketPacket beta appArg lamDomain piDomain transport routes
        ledger name bundle pkg ->
      Cont beta appArg consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory beta ∧ UnaryHistory appArg ∧ UnaryHistory consumer ∧
            Cont beta appArg consumer ∧ PkgSig bundle consumer pkg ∧
              PkgSig bundle name pkg := by
  intro packet consumerRoute consumerPkg
  obtain ⟨betaUnary, appArgUnary, _lamDomainUnary, _piDomainUnary, _transportUnary,
    _routesUnary, _ledgerUnary, _nameUnary, _betaAppTransport, _domainRoute,
    _transportRoutesLedger, _ledgerNameBeta, namePkg⟩ := packet
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed betaUnary appArgUnary consumerRoute
  exact
    ⟨betaUnary, appArgUnary, consumerUnary, consumerRoute, consumerPkg, namePkg⟩

end BEDC.Derived.SubjectReductionDischargeSocketUp
