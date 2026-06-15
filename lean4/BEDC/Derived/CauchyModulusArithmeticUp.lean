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

end BEDC.Derived.CauchyModulusArithmeticUp
