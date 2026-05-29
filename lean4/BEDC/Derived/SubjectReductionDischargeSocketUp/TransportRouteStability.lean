import BEDC.Derived.SubjectReductionDischargeSocketUp

namespace BEDC.Derived.SubjectReductionDischargeSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SubjectReductionDischargeSocketPacket_transport_route_stability [AskSetup]
    [PackageSetup] {beta appArg lamDomain piDomain transport routes ledger name betaRead
      lamRead ledgerRead replayRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubjectReductionDischargeSocketPacket beta appArg lamDomain piDomain transport routes
        ledger name bundle pkg →
      Cont beta appArg betaRead →
        Cont lamDomain piDomain lamRead →
          Cont transport routes ledgerRead →
            Cont ledgerRead name replayRead →
              PkgSig bundle replayRead pkg →
                UnaryHistory betaRead ∧ UnaryHistory lamRead ∧ UnaryHistory ledgerRead ∧
                  UnaryHistory replayRead ∧ Cont beta appArg betaRead ∧
                    Cont lamDomain piDomain lamRead ∧ Cont transport routes ledgerRead ∧
                      Cont ledgerRead name replayRead ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro packet betaRoute lamRoute ledgerRoute replayRoute replayPkg
  obtain ⟨betaUnary, appArgUnary, lamDomainUnary, piDomainUnary, transportUnary,
    routesUnary, _ledgerUnary, nameUnary, _betaAppTransport, _domainRoute,
    _transportRoutesLedger, _ledgerNameBeta, namePkg⟩ := packet
  have betaReadUnary : UnaryHistory betaRead :=
    unary_cont_closed betaUnary appArgUnary betaRoute
  have lamReadUnary : UnaryHistory lamRead :=
    unary_cont_closed lamDomainUnary piDomainUnary lamRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed transportUnary routesUnary ledgerRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed ledgerReadUnary nameUnary replayRoute
  exact
    ⟨betaReadUnary, lamReadUnary, ledgerReadUnary, replayReadUnary, betaRoute, lamRoute,
      ledgerRoute, replayRoute, namePkg, replayPkg⟩

end BEDC.Derived.SubjectReductionDischargeSocketUp
