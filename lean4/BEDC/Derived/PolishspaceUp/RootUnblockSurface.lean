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

def PolishSpaceRootUnblockSurface [AskSetup] [PackageSetup]
    (metric complete separable stream readback ledger transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory metric ∧ UnaryHistory complete ∧ UnaryHistory separable ∧
    UnaryHistory stream ∧ UnaryHistory readback ∧ UnaryHistory ledger ∧
      UnaryHistory transport ∧ Cont metric complete (append metric complete) ∧
        Cont metric separable (append metric separable) ∧
          Cont ledger transport replay ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle localName pkg

end BEDC.Derived.PolishspaceUp
