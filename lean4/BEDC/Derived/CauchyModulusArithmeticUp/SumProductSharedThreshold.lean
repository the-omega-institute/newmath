import BEDC.Derived.CauchyModulusArithmeticUp

namespace BEDC.Derived.CauchyModulusArithmeticUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusArithmeticCarrier_sum_product_shared_threshold
    [AskSetup] [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow
      transport replay provenance localName thresholdRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
        window readback sealRow transport replay provenance localName bundle pkg →
      Cont meet dyadic thresholdRead →
        Cont sum product thresholdRead →
          hsame transport (append meet dyadic) →
            UnaryHistory meet ∧ UnaryHistory dyadic ∧ UnaryHistory sum ∧
              UnaryHistory product ∧ UnaryHistory thresholdRead ∧ Cont meet dyadic sum ∧
                Cont meet dyadic product ∧ Cont meet dyadic thresholdRead ∧
                  Cont sum product thresholdRead ∧ hsame transport (append meet dyadic) ∧
                    PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame
  intro carrier thresholdRoute sumProductRoute transportAnchor
  obtain
    ⟨_stream0Unary, _stream1Unary, _modulus0Unary, _modulus1Unary, meetUnary,
      sumUnary, productUnary, dyadicUnary, _windowUnary, _readbackUnary,
      _sealUnary, _transportUnary, _meetRoute, sumRoute, productRoute, _sealRoute,
      _provenanceRoute, localPackage⟩ := carrier
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed meetUnary dyadicUnary thresholdRoute
  exact
    ⟨meetUnary, dyadicUnary, sumUnary, productUnary, thresholdUnary, sumRoute,
      productRoute, thresholdRoute, sumProductRoute, transportAnchor, localPackage⟩

end BEDC.Derived.CauchyModulusArithmeticUp
