import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.KolmogorovContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def KolmogorovContinuityCarrier [AskSetup] [PackageSetup]
    (difference moment stream readback realSeal endpoint transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory difference ∧ UnaryHistory moment ∧ UnaryHistory stream ∧
    UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory endpoint ∧
      UnaryHistory transport ∧ Cont difference moment stream ∧
        Cont stream readback realSeal ∧ Cont realSeal endpoint transport ∧
          Cont transport replay provenance ∧ PkgSig bundle localName pkg

end BEDC.Derived.KolmogorovContinuityUp
