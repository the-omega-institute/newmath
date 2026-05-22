import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SecondCountableUp [AskSetup] [PackageSetup]
    (source topology metric base dyadic stream realSeal transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory topology ∧ UnaryHistory metric ∧ UnaryHistory base ∧
    UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory realSeal ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont source base replay ∧ Cont metric dyadic stream ∧
          Cont stream topology realSeal ∧ Cont transport replay provenance ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

end BEDC.Derived
