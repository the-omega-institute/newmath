import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_open_phase_exit_spine [AskSetup] [PackageSetup]
    {source refined meet selector budget window readback sealRow transport route provenance cert
      windowRead readbackRead sealRead exitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier source refined meet selector budget window readback sealRow
        transport route provenance cert bundle pkg ->
      Cont budget window windowRead ->
        Cont window readback readbackRead ->
          Cont readback sealRow sealRead ->
            Cont windowRead sealRead exitRead ->
              PkgSig bundle windowRead pkg ->
                PkgSig bundle readbackRead pkg ->
                  PkgSig bundle sealRead pkg ->
                    PkgSig bundle exitRead pkg ->
                      UnaryHistory source ∧ UnaryHistory refined ∧ UnaryHistory meet ∧
                        UnaryHistory budget ∧ UnaryHistory window ∧ UnaryHistory readback ∧
                          UnaryHistory sealRow ∧ UnaryHistory windowRead ∧
                            UnaryHistory readbackRead ∧ UnaryHistory sealRead ∧
                              UnaryHistory exitRead ∧ Cont budget window windowRead ∧
                                Cont window readback readbackRead ∧ Cont readback sealRow sealRead ∧
                                  Cont windowRead sealRead exitRead ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle exitRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier budgetWindowRead windowReadbackRead readbackSealRead exitRoute _windowPkg
    _readbackPkg _sealPkg exitPkg
  obtain ⟨sourceUnary, refinedUnary, meetUnary, _selectorUnary, budgetUnary, windowUnary,
    readbackUnary, sealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary,
    _sourceRefinedMeet, _meetSelectorBudget, _budgetWindowReadback, _readbackSealTransport,
    provenancePkg, _transportCert⟩ := carrier
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed budgetUnary windowUnary budgetWindowRead
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary readbackUnary windowReadbackRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary sealUnary readbackSealRead
  have exitReadUnary : UnaryHistory exitRead :=
    unary_cont_closed windowReadUnary sealReadUnary exitRoute
  exact
    ⟨sourceUnary, refinedUnary, meetUnary, budgetUnary, windowUnary, readbackUnary, sealUnary,
      windowReadUnary, readbackReadUnary, sealReadUnary, exitReadUnary, budgetWindowRead,
      windowReadbackRead, readbackSealRead, exitRoute, provenancePkg, exitPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
