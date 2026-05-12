import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyLimitModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyLimitModulusPacket [AskSetup] [PackageSetup]
    (input modulus precision threshold window readback dyadicLedger sealRow provenance cert :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory input ∧ UnaryHistory modulus ∧ UnaryHistory precision ∧
    UnaryHistory sealRow ∧ UnaryHistory provenance ∧ Cont input modulus threshold ∧
      Cont threshold precision window ∧ Cont window readback dyadicLedger ∧
        Cont dyadicLedger sealRow cert ∧ PkgSig bundle provenance pkg

end BEDC.Derived.RegularCauchyLimitModulusUp
