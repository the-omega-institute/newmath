import BEDC.Derived.CauchyModulusArithmeticUp

namespace BEDC.Derived.CauchyModulusArithmeticUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusArithmeticCarrier_public_exactness [AskSetup] [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow
      transport replay provenance localName sumProductRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
        window readback sealRow transport replay provenance localName bundle pkg ->
      Cont sum product sumProductRead ->
        Cont sealRow transport publicRead ->
          PkgSig bundle publicRead pkg ->
            UnaryHistory meet ∧ UnaryHistory dyadic ∧ UnaryHistory sum ∧
              UnaryHistory product ∧ UnaryHistory readback ∧ UnaryHistory sealRow ∧
                UnaryHistory publicRead ∧ Cont meet dyadic sum ∧
                  Cont meet dyadic product ∧ Cont sum product sumProductRead ∧
                    Cont sealRow transport publicRead ∧ PkgSig bundle localName pkg ∧
                      PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier sumProductRoute publicRoute publicPackage
  obtain
    ⟨_stream0Unary, _stream1Unary, _modulus0Unary, _modulus1Unary, meetUnary,
      sumUnary, productUnary, dyadicUnary, _windowUnary, readbackUnary, sealUnary,
      transportUnary, _meetRoute, sumRoute, productRoute, _sealRoute, _provenanceRoute,
      localPackage⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary transportUnary publicRoute
  exact
    ⟨meetUnary, dyadicUnary, sumUnary, productUnary, readbackUnary, sealUnary,
      publicUnary, sumRoute, productRoute, sumProductRoute, publicRoute, localPackage,
      publicPackage⟩

end BEDC.Derived.CauchyModulusArithmeticUp
