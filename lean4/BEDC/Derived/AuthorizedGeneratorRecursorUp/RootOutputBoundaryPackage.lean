import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def AuthorizedGeneratorRecursorRootOutputBoundaryPackage [AskSetup] [PackageSetup]
    (I E M B D O A H C P G N outputRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig
  AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg /\
    Cont B D outputRead /\ Cont H C P /\ PkgSig bundle O pkg /\ PkgSig bundle N pkg

end BEDC.Derived.AuthorizedGeneratorRecursorUp
