import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicIntervalCoverObligationSurface [AskSetup] [PackageSetup]
    (L U M R V W Q A H C P N : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  UnaryHistory L ∧ UnaryHistory U ∧ UnaryHistory M ∧ UnaryHistory R ∧
    UnaryHistory V ∧ UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory A ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
          SemanticNameCert
            (fun row : BHist => hsame row N ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨ hsame row V ∨
                hsame row W ∨ hsame row Q ∨ hsame row A ∨ hsame row N)
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle N pkg)
            hsame

end BEDC.Derived.DyadicIntervalCoverUp
