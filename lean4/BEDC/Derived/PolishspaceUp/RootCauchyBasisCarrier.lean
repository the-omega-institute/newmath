import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PolishspaceRootCauchyBasisCarrier [AskSetup] [PackageSetup]
    (metric complete separable stream readback ledger alignment transport route provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory metric ∧ UnaryHistory complete ∧ UnaryHistory separable ∧
    UnaryHistory stream ∧ UnaryHistory readback ∧ UnaryHistory ledger ∧
      UnaryHistory alignment ∧ UnaryHistory transport ∧ Cont metric complete alignment ∧
        Cont alignment stream readback ∧ Cont ledger transport route ∧
          PkgSig bundle provenance pkg

end BEDC.Derived.PolishspaceUp
