import BEDC.Derived.SubjectReductionDischargeSocketUp

namespace BEDC.Derived.SubjectReductionDischargeSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SubjectReductionDischargeSocketPacket_transport_stability [AskSetup] [PackageSetup]
    {beta appArg lamDomain piDomain transport routes ledger name beta' appArg'
      lamDomain' piDomain' transport' routes' ledger' name' betaRead lamRead
      ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubjectReductionDischargeSocketPacket beta appArg lamDomain piDomain transport routes
        ledger name bundle pkg →
      hsame beta beta' →
        hsame appArg appArg' →
          hsame lamDomain lamDomain' →
            hsame piDomain piDomain' →
              hsame transport transport' →
                hsame routes routes' →
                  hsame ledger ledger' →
                    hsame name name' →
                      Cont beta' appArg' betaRead →
                        Cont lamDomain' piDomain' lamRead →
                          Cont transport' routes' ledgerRead →
                            PkgSig bundle ledgerRead pkg →
                              UnaryHistory betaRead ∧ UnaryHistory lamRead ∧
                                UnaryHistory ledgerRead ∧ Cont beta' appArg' betaRead ∧
                                  Cont lamDomain' piDomain' lamRead ∧
                                    Cont transport' routes' ledgerRead ∧
                                      PkgSig bundle name pkg ∧
                                        PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory ProbeBundle PkgSig
  intro packet sameBeta sameAppArg sameLamDomain _samePiDomain sameTransport sameRoutes
    _sameLedger _sameName betaReadRoute lamReadRoute ledgerReadRoute ledgerReadPkg
  obtain ⟨betaUnary, appArgUnary, lamDomainUnary, _piDomainUnary, transportUnary,
    routesUnary, _ledgerUnary, _nameUnary, _betaAppTransport, _domainRoute,
    _transportRoutesLedger, _ledgerNameBeta, namePkg⟩ := packet
  have betaPrimeUnary : UnaryHistory beta' :=
    unary_transport betaUnary sameBeta
  have appArgPrimeUnary : UnaryHistory appArg' :=
    unary_transport appArgUnary sameAppArg
  have lamDomainPrimeUnary : UnaryHistory lamDomain' :=
    unary_transport lamDomainUnary sameLamDomain
  have transportPrimeUnary : UnaryHistory transport' :=
    unary_transport transportUnary sameTransport
  have routesPrimeUnary : UnaryHistory routes' :=
    unary_transport routesUnary sameRoutes
  have betaReadUnary : UnaryHistory betaRead :=
    unary_cont_closed betaPrimeUnary appArgPrimeUnary betaReadRoute
  have lamReadUnary : UnaryHistory lamRead :=
    unary_cont_closed lamDomainPrimeUnary (unary_transport _piDomainUnary _samePiDomain)
      lamReadRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed transportPrimeUnary routesPrimeUnary ledgerReadRoute
  exact
    ⟨betaReadUnary, lamReadUnary, ledgerReadUnary, betaReadRoute, lamReadRoute,
      ledgerReadRoute, namePkg, ledgerReadPkg⟩

end BEDC.Derived.SubjectReductionDischargeSocketUp
