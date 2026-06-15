import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyModulusArithmeticUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyModulusArithmeticCarrier [AskSetup] [PackageSetup]
    (stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow transport
      replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream0 ∧ UnaryHistory stream1 ∧ UnaryHistory modulus0 ∧
    UnaryHistory modulus1 ∧ UnaryHistory meet ∧ UnaryHistory sum ∧
      UnaryHistory product ∧ UnaryHistory dyadic ∧ UnaryHistory window ∧
        UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
          Cont modulus0 modulus1 meet ∧ Cont meet dyadic sum ∧
            Cont meet dyadic product ∧ Cont window readback sealRow ∧
              Cont transport replay provenance ∧ PkgSig bundle localName pkg

theorem CauchyModulusArithmeticCarrier_sum_meet_closure [AskSetup] [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow transport
      replay provenance localName sumProductRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
        window readback sealRow transport replay provenance localName bundle pkg ->
      Cont sum product sumProductRead ->
        hsame transport (append meet dyadic) ->
          UnaryHistory meet ∧ UnaryHistory sum ∧ UnaryHistory product ∧
            UnaryHistory dyadic ∧ UnaryHistory sumProductRead ∧ Cont meet dyadic sum ∧
              Cont meet dyadic product ∧ Cont sum product sumProductRead ∧
                hsame transport (append meet dyadic) ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont PkgSig
  intro carrier sumProductRoute transportAnchor
  cases carrier with
  | intro uStream0 rest =>
      cases rest with
      | intro uStream1 rest =>
          cases rest with
          | intro uModulus0 rest =>
              cases rest with
              | intro uModulus1 rest =>
                  cases rest with
                  | intro uMeet rest =>
                      cases rest with
                      | intro uSum rest =>
                          cases rest with
                          | intro uProduct rest =>
                              cases rest with
                              | intro uDyadic rest =>
                                  cases rest with
                                  | intro uWindow rest =>
                                      cases rest with
                                      | intro uReadback rest =>
                                          cases rest with
                                          | intro uSealRow rest =>
                                              cases rest with
                                              | intro uTransport rest =>
                                                  cases rest with
                                                  | intro moduliMeet rest =>
                                                      cases rest with
                                                      | intro meetDyadicSum rest =>
                                                          cases rest with
                                                          | intro meetDyadicProduct rest =>
                                                              cases rest with
                                                              | intro windowReadbackSeal rest =>
                                                                  cases rest with
                                                                  | intro transportReplayProvenance
                                                                      pkgSig =>
                                                                      constructor
                                                                      · exact uMeet
                                                                      · constructor
                                                                        · exact uSum
                                                                        · constructor
                                                                          · exact uProduct
                                                                          · constructor
                                                                            · exact uDyadic
                                                                            · constructor
                                                                              · exact
                                                                                  unary_cont_closed
                                                                                    uSum uProduct
                                                                                    sumProductRoute
                                                                              · constructor
                                                                                · exact meetDyadicSum
                                                                                · constructor
                                                                                  · exact meetDyadicProduct
                                                                                  · constructor
                                                                                    · exact
                                                                                        sumProductRoute
                                                                                    · constructor
                                                                                      · exact
                                                                                          transportAnchor
                                                                                      · exact pkgSig

end BEDC.Derived.CauchyModulusArithmeticUp
