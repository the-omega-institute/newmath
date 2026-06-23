import BEDC.Derived.CompactOperatorUp

namespace BEDC.Derived.CompactOperatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def CompactOperatorApproximationScheme [AskSetup] [PackageSetup]
    (source target operator imageNet modulus transport replay provenance localName compactRead
      approximationRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  BEDC.Derived.CompactOperatorCarrier source target operator imageNet modulus transport replay
      provenance localName bundle pkg ∧
    Cont operator imageNet compactRead ∧ Cont compactRead modulus approximationRead ∧
      PkgSig bundle approximationRead pkg

end BEDC.Derived.CompactOperatorUp
