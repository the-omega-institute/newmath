import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealOscillationCarrier [AskSetup] [PackageSetup]
    (realSeal oscillation clamp squeeze tolerance window readback transport replay provenance
      nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory realSeal ∧ UnaryHistory oscillation ∧ UnaryHistory clamp ∧
    UnaryHistory squeeze ∧ UnaryHistory tolerance ∧ UnaryHistory window ∧
      UnaryHistory readback ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory nameCert ∧
          Cont oscillation clamp squeeze ∧ Cont squeeze tolerance window ∧
            Cont window readback transport ∧ Cont transport replay nameCert ∧
              PkgSig bundle provenance pkg

end BEDC.Derived.RealOscillationUp
