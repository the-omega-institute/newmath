import BEDC.Derived.CauchyModulusArithmeticUp

namespace BEDC.Derived.CauchyModulusArithmeticUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusArithmeticCarrier_real_seal_congruence [AskSetup] [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow
      transport replay provenance localName sumRead productRead sealRead transportedSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
        window readback sealRow transport replay provenance localName bundle pkg ->
      Cont meet dyadic sumRead ->
        Cont meet dyadic productRead ->
          Cont sumRead productRead sealRead ->
            hsame sealRead transportedSeal ->
              PkgSig bundle transportedSeal pkg ->
                UnaryHistory sealRead ∧ UnaryHistory transportedSeal ∧
                  Cont meet dyadic sumRead ∧ Cont meet dyadic productRead ∧
                    Cont sumRead productRead sealRead ∧ hsame sealRead transportedSeal ∧
                      PkgSig bundle localName pkg ∧ PkgSig bundle transportedSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier sumRoute productRoute sealRoute sealSame transportedPackage
  obtain
    ⟨_stream0Unary, _stream1Unary, _modulus0Unary, _modulus1Unary, meetUnary,
      _sumUnary, _productUnary, dyadicUnary, _windowUnary, _readbackUnary, _sealRowUnary,
      _transportUnary, _meetRoute, _sumCarrierRoute, _productCarrierRoute, _windowRoute,
      _provenanceRoute, localPackage⟩ := carrier
  have sumReadUnary : UnaryHistory sumRead :=
    unary_cont_closed meetUnary dyadicUnary sumRoute
  have productReadUnary : UnaryHistory productRead :=
    unary_cont_closed meetUnary dyadicUnary productRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed sumReadUnary productReadUnary sealRoute
  have transportedUnary : UnaryHistory transportedSeal :=
    unary_transport sealReadUnary sealSame
  exact
    ⟨sealReadUnary, transportedUnary, sumRoute, productRoute, sealRoute, sealSame,
      localPackage, transportedPackage⟩

end BEDC.Derived.CauchyModulusArithmeticUp
