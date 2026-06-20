import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BoundedSearchRefutationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Gap
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BoundedSearchRefutationCarrier [AskSetup] [PackageSetup]
    (proposition budget frontier witness gap transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory proposition ∧ UnaryHistory budget ∧ UnaryHistory frontier ∧
    UnaryHistory witness ∧ UnaryHistory gap ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      Cont proposition budget frontier ∧ Cont frontier witness route ∧
        Cont frontier gap transport ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

end BEDC.Derived.BoundedSearchRefutationUp
