import BEDC.Derived.CauchyModulusArithmeticUp

namespace BEDC.Derived.CauchyModulusArithmeticUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusArithmeticCarrier_obligation_closure [AskSetup] [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow
      transport replay provenance localName thresholdRead productTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
        window readback sealRow transport replay provenance localName bundle pkg ->
      Cont meet dyadic thresholdRead ->
        Cont product window productTail ->
          PkgSig bundle thresholdRead pkg ->
            PkgSig bundle productTail pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row stream0 ∨ hsame row stream1 ∨ hsame row meet ∨
                      hsame row sum ∨ hsame row product ∨ hsame row sealRow)
                  (fun row : BHist =>
                    hsame row sealRow ∧ Cont window readback sealRow ∧
                      Cont transport replay provenance ∧ PkgSig bundle localName pkg)
                  hsame ∧ Cont modulus0 modulus1 meet ∧ Cont meet dyadic sum ∧
                Cont meet dyadic product ∧ Cont meet dyadic thresholdRead ∧
              Cont product window productTail ∧ PkgSig bundle localName pkg ∧
            PkgSig bundle thresholdRead pkg ∧ PkgSig bundle productTail pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier thresholdRoute productTailRoute thresholdPackage productTailPackage
  obtain
    ⟨cert, meetRoute, sumRoute, productRoute, _sealRoute, _provenanceRoute,
      localPackage⟩ :=
    CauchyModulusArithmeticCarrier_namecert_obligations carrier
  exact
    ⟨cert, meetRoute, sumRoute, productRoute, thresholdRoute, productTailRoute,
      localPackage, thresholdPackage, productTailPackage⟩

end BEDC.Derived.CauchyModulusArithmeticUp
