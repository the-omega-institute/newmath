import BEDC.Derived.TerminationRefusalBoundaryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TerminationRefusalBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TerminationRefusalBoundaryCarrier [AskSetup] [PackageSetup]
    (S I T F U H C P N traceRead refusalRead namedRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig
  UnaryHistory S ∧ UnaryHistory I ∧ UnaryHistory T ∧ UnaryHistory F ∧
    UnaryHistory U ∧ UnaryHistory H ∧ Cont T F traceRead ∧ Cont U H refusalRead ∧
      Cont C P namedRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

end BEDC.Derived.TerminationRefusalBoundaryUp
