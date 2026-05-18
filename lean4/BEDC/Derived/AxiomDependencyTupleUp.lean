import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AxiomDependencyTupleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AxiomDependencyTupleCarrier [AskSetup] [PackageSetup]
    (mode witness supply transport route provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory mode ∧ UnaryHistory witness ∧ UnaryHistory supply ∧
    UnaryHistory transport ∧ UnaryHistory provenance ∧ Cont mode supply route ∧
      Cont route witness transport ∧ Cont transport provenance localName ∧
        PkgSig bundle provenance pkg ∧ hsame localName (append provenance supply)

end BEDC.Derived.AxiomDependencyTupleUp
