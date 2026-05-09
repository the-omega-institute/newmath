import BEDC.Derived.ObservableUp

namespace BEDC.Derived.ObservableUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ObservableExpectationInterfacePacket [AskSetup] [PackageSetup]
    (hilbert operator witness spectrum expectation provenance ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory hilbert ∧ UnaryHistory operator ∧ UnaryHistory witness ∧
    UnaryHistory spectrum ∧ UnaryHistory expectation ∧ PkgSig bundle provenance pkg ∧
      Cont operator expectation ledger ∧ hsame provenance BHist.Empty

end BEDC.Derived.ObservableUp
