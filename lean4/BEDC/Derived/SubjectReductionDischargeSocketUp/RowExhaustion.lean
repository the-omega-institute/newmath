import BEDC.Derived.SubjectReductionDischargeSocketUp

namespace BEDC.Derived.SubjectReductionDischargeSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SubjectReductionDischargeSocketPacket_row_exhaustion [AskSetup] [PackageSetup]
    {beta appArg lamDomain piDomain transport routes ledger name betaRead lamRead
      ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubjectReductionDischargeSocketPacket beta appArg lamDomain piDomain transport routes
        ledger name bundle pkg →
      Cont beta appArg betaRead →
        Cont lamDomain piDomain lamRead →
          Cont transport routes ledgerRead →
            PkgSig bundle ledgerRead pkg →
              UnaryHistory beta ∧ UnaryHistory appArg ∧ UnaryHistory lamDomain ∧
                UnaryHistory piDomain ∧ UnaryHistory betaRead ∧ UnaryHistory lamRead ∧
                  UnaryHistory ledgerRead ∧ Cont beta appArg betaRead ∧
                    Cont lamDomain piDomain lamRead ∧ Cont transport routes ledgerRead ∧
                      Cont ledger name beta ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet betaReadRoute lamReadRoute ledgerReadRoute ledgerReadPkg
  obtain ⟨betaUnary, appArgUnary, lamDomainUnary, piDomainUnary, transportUnary,
    routesUnary, _ledgerUnary, _nameUnary, _betaAppTransport, _domainRoute,
    _transportRoutesLedger, ledgerNameBeta, namePkg⟩ := packet
  have betaReadUnary : UnaryHistory betaRead :=
    unary_cont_closed betaUnary appArgUnary betaReadRoute
  have lamReadUnary : UnaryHistory lamRead :=
    unary_cont_closed lamDomainUnary piDomainUnary lamReadRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed transportUnary routesUnary ledgerReadRoute
  exact
    ⟨betaUnary, appArgUnary, lamDomainUnary, piDomainUnary, betaReadUnary, lamReadUnary,
      ledgerReadUnary, betaReadRoute, lamReadRoute, ledgerReadRoute, ledgerNameBeta, namePkg,
      ledgerReadPkg⟩

end BEDC.Derived.SubjectReductionDischargeSocketUp
