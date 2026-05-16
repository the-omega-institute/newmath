import BEDC.Derived.FiniteObservationBudgetSelectorUp
import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.FiniteObservationBudgetSelectorUp

theorem UniformCauchyCriterionPacket_finite_observation_budget_pullback [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name budget source
      selectorWindow dyadic readback endpoint selectorTransport selectorRoute selectorProvenance
      selectorName publicRead selectorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      FiniteObservationBudgetSelectorCarrier budget source selectorWindow dyadic readback endpoint
        selectorTransport selectorRoute selectorProvenance selectorName →
        hsame windows selectorWindow →
          hsame tolerance dyadic →
            hsame tail readback →
              hsame sealRow endpoint →
                Cont index tail publicRead →
                  Cont readback endpoint selectorRead →
                    PkgSig bundle publicRead pkg →
                      PkgSig bundle selectorRead pkg →
                        UnaryHistory publicRead ∧ UnaryHistory selectorRead ∧
                          hsame windows selectorWindow ∧ hsame tolerance dyadic ∧
                            hsame tail readback ∧ hsame sealRow endpoint ∧
                              PkgSig bundle publicRead pkg ∧
                                PkgSig bundle selectorRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet selector sameWindow sameDyadic sameReadback sameEndpoint indexTailPublic
    readbackEndpointSelector publicPkg selectorPkg
  obtain ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    _sealUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, _namePkg⟩ := packet
  obtain ⟨budgetUnary, sourceUnary, dyadicUnary, endpointUnary, budgetSourceWindow,
    windowDyadicReadback, _readbackEndpointRoute, _sameSelectorName⟩ := selector
  have selectorWindowUnary : UnaryHistory selectorWindow :=
    unary_cont_closed budgetUnary sourceUnary budgetSourceWindow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectorWindowUnary dyadicUnary windowDyadicReadback
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed indexUnary tailUnary indexTailPublic
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed readbackUnary endpointUnary readbackEndpointSelector
  exact
    ⟨publicUnary, selectorUnary, sameWindow, sameDyadic, sameReadback, sameEndpoint,
      publicPkg, selectorPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
