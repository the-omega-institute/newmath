import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RiemannHilbertUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RiemannHilbertBHistBridgePacket [AskSetup] [PackageSetup]
    (derived sheaf regularHolonomic deRhamReadback localSystem gluing provenance
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory derived ∧
    UnaryHistory sheaf ∧
      UnaryHistory regularHolonomic ∧
        Cont derived deRhamReadback localSystem ∧
          Cont localSystem sheaf gluing ∧
            Cont gluing regularHolonomic endpoint ∧ PkgSig bundle provenance pkg

end BEDC.Derived.RiemannHilbertUp
