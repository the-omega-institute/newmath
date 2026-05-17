import BEDC.Derived.RegularCauchyModulusNormalizerUp

namespace BEDC.Derived.RegularCauchyModulusNormalizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyModulusNormalizerCarrier_budget_pullback_exhaustion [AskSetup]
    [PackageSetup]
    {x y muX muY meet window dyadic readback sealRow transport route provenance name
      budgetRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback sealRow
        transport route provenance name bundle pkg →
      Cont window dyadic budgetRead →
        Cont budgetRead sealRow terminalRead →
          PkgSig bundle budgetRead pkg →
            PkgSig bundle terminalRead pkg →
              UnaryHistory meet ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
                UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory budgetRead ∧
                  UnaryHistory terminalRead ∧ Cont muX muY meet ∧
                    Cont meet window dyadic ∧ Cont window dyadic budgetRead ∧
                      Cont budgetRead sealRow terminalRead ∧ PkgSig bundle budgetRead pkg ∧
                        PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier windowDyadicBudget budgetSealTerminal budgetPkg terminalPkg
  rcases carrier with
    ⟨_xUnary, _yUnary, _muXUnary, _muYUnary, meetUnary, windowUnary, dyadicUnary,
      readbackUnary, sealUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
      sourceMeet, meetWindowDyadic, _dyadicReadbackSeal, _sealTransportRoute,
      _routeProvenanceName, _meetPkg, _namePkg⟩
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicBudget
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed budgetUnary sealUnary budgetSealTerminal
  exact
    ⟨meetUnary, windowUnary, dyadicUnary, readbackUnary, sealUnary, budgetUnary,
      terminalUnary, sourceMeet, meetWindowDyadic, windowDyadicBudget, budgetSealTerminal,
      budgetPkg, terminalPkg⟩

end BEDC.Derived.RegularCauchyModulusNormalizerUp
