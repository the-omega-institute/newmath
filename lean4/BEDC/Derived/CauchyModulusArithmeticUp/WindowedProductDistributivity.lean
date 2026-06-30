import BEDC.Derived.CauchyModulusArithmeticUp

namespace BEDC.Derived.CauchyModulusArithmeticUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusArithmeticCarrier_windowed_product_distributivity
    [AskSetup] [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow transport
      replay provenance localName productBudget distributivityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
        window readback sealRow transport replay provenance localName bundle pkg ->
      Cont sum product productBudget ->
        Cont productBudget window distributivityRead ->
          hsame transport (append meet dyadic) ->
            PkgSig bundle distributivityRead pkg ->
              UnaryHistory meet ∧ UnaryHistory sum ∧ UnaryHistory product ∧
                UnaryHistory dyadic ∧ UnaryHistory window ∧ UnaryHistory productBudget ∧
                  UnaryHistory distributivityRead ∧ Cont meet dyadic sum ∧
                    Cont meet dyadic product ∧ Cont sum product productBudget ∧
                      Cont productBudget window distributivityRead ∧
                        hsame transport (append meet dyadic) ∧ PkgSig bundle localName pkg ∧
                          PkgSig bundle distributivityRead pkg := by
  -- BEDC touchpoint anchor: CauchyModulusArithmeticCarrier BHist ProbeBundle Pkg hsame Cont
  intro carrier productRoute distributivityRoute transportAnchor distributivityPackage
  obtain
    ⟨_stream0Unary, _stream1Unary, _modulus0Unary, _modulus1Unary, meetUnary,
      sumUnary, productUnary, dyadicUnary, windowUnary, _readbackUnary, _sealRowUnary,
      _transportUnary, _meetRoute, sumRoute, productMeetRoute, _windowReadbackSeal,
      _transportReplayProvenance, carrierPackage⟩ := carrier
  have productBudgetUnary : UnaryHistory productBudget :=
    unary_cont_closed sumUnary productUnary productRoute
  have distributivityUnary : UnaryHistory distributivityRead :=
    unary_cont_closed productBudgetUnary windowUnary distributivityRoute
  exact
    ⟨meetUnary, sumUnary, productUnary, dyadicUnary, windowUnary, productBudgetUnary,
      distributivityUnary, sumRoute, productMeetRoute, productRoute, distributivityRoute,
      transportAnchor, carrierPackage, distributivityPackage⟩

end BEDC.Derived.CauchyModulusArithmeticUp
