import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def AuthorizedGeneratorRecursorReadinessRoute [AskSetup] [PackageSetup]
    (signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert generator compiler refusal replay : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig
  AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
      transport continuation provenance boundary localCert bundle pkg ∧
    Cont signature eliminator generator ∧
      Cont generator compiler output ∧
        Cont boundary audit refusal ∧
          Cont transport continuation replay ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle localCert pkg

end BEDC.Derived.AuthorizedGeneratorRecursorUp
