import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteLebesgueNumberPhaseRealRadiusConsumerLedger [AskSetup] [PackageSetup]
    (cover ball mesh dyadicFace stream regular real compact continuous uniform transport
      replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory cover ∧ UnaryHistory ball ∧ UnaryHistory mesh ∧ UnaryHistory dyadicFace ∧
    UnaryHistory stream ∧ UnaryHistory regular ∧ UnaryHistory real ∧ UnaryHistory compact ∧
      UnaryHistory continuous ∧ UnaryHistory uniform ∧ UnaryHistory transport ∧
        UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

end BEDC.Derived.FiniteLebesgueNumberUp
