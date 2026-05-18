import BEDC.Derived.AuthorizedGeneratorRecursorUp.TasteGate
import BEDC.FKernel.Package

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AuthorizedGeneratorRecursorCarrier [AskSetup] [PackageSetup]
    (signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  UnaryHistory signature ∧ UnaryHistory eliminator ∧ UnaryHistory motive ∧
    UnaryHistory branch ∧ UnaryHistory descent ∧ UnaryHistory output ∧ UnaryHistory audit ∧
      UnaryHistory transport ∧ UnaryHistory continuation ∧ UnaryHistory provenance ∧
        UnaryHistory boundary ∧ UnaryHistory localCert ∧ Cont signature eliminator motive ∧
          Cont motive branch descent ∧ Cont descent output audit ∧
            hsame transport (append audit continuation) ∧ PkgSig bundle provenance pkg

end BEDC.Derived.AuthorizedGeneratorRecursorUp
