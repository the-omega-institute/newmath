import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ClosedTermSubstitutionBoundaryRootOperationSurface [AskSetup] [PackageSetup]
    (source value depth sourceClosed valueClosed shift substitution ledger audit transport route
      provenance name : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory source ∧ UnaryHistory value ∧ UnaryHistory depth ∧
    UnaryHistory sourceClosed ∧ UnaryHistory valueClosed ∧ UnaryHistory shift ∧
      UnaryHistory substitution ∧ Cont sourceClosed valueClosed ledger ∧
        Cont shift substitution audit ∧ Cont ledger audit transport ∧
          Cont transport route provenance ∧ PkgSig bundle name pkg

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
