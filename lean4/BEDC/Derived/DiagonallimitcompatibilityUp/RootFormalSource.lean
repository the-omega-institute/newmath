import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DiagonalLimitCompatibilityRootFormalSource [AskSetup] [PackageSetup]
    (budget selector window regseq realSeal transport route provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory budget ∧ UnaryHistory selector ∧ UnaryHistory window ∧
    UnaryHistory regseq ∧ UnaryHistory realSeal ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory cert ∧
        Cont budget selector window ∧ Cont window regseq realSeal ∧
          Cont transport route cert ∧ PkgSig bundle provenance pkg

end BEDC.Derived.DiagonallimitcompatibilityUp
