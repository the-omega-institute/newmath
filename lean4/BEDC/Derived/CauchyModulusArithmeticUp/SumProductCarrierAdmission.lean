import BEDC.Derived.CauchyModulusArithmeticUp

namespace BEDC.Derived.CauchyModulusArithmeticUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusArithmeticCarrier_sum_product_carrier_admission
    [AskSetup] [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow
      transport replay provenance localName sumProductRead productTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
        window readback sealRow transport replay provenance localName bundle pkg ->
      Cont sum product sumProductRead ->
        Cont product window productTail ->
          PkgSig bundle productTail pkg ->
            UnaryHistory sum ∧ UnaryHistory product ∧ UnaryHistory dyadic ∧
              UnaryHistory window ∧ UnaryHistory readback ∧ UnaryHistory sealRow ∧
                UnaryHistory sumProductRead ∧ UnaryHistory productTail ∧
                  Cont meet dyadic sum ∧ Cont meet dyadic product ∧
                    Cont sum product sumProductRead ∧ Cont product window productTail ∧
                      Cont window readback sealRow ∧ Cont transport replay provenance ∧
                        PkgSig bundle localName pkg ∧ PkgSig bundle productTail pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier sumProductRoute productTailRoute productTailPackage
  obtain
    ⟨_stream0Unary, _stream1Unary, _modulus0Unary, _modulus1Unary, _meetUnary,
      sumUnary, productUnary, dyadicUnary, windowUnary, readbackUnary, sealUnary,
      _transportUnary, _meetRoute, sumRoute, productRoute, sealRoute, provenanceRoute,
      localPackage⟩ := carrier
  have sumProductUnary : UnaryHistory sumProductRead :=
    unary_cont_closed sumUnary productUnary sumProductRoute
  have productTailUnary : UnaryHistory productTail :=
    unary_cont_closed productUnary windowUnary productTailRoute
  exact
    ⟨sumUnary, productUnary, dyadicUnary, windowUnary, readbackUnary, sealUnary,
      sumProductUnary, productTailUnary, sumRoute, productRoute, sumProductRoute,
      productTailRoute, sealRoute, provenanceRoute, localPackage, productTailPackage⟩

end BEDC.Derived.CauchyModulusArithmeticUp
