import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CylinderObjectUp : Type where
  | mk (model object endpoint0 endpoint1 cylinder weak factor homotopy
      replacement provenance name : BHist) : CylinderObjectUp
  deriving DecidableEq

end BEDC.Derived

namespace BEDC.Derived.CylinderObjectUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CylinderObjectCarrier [AskSetup] [PackageSetup]
    (model object endpoint0 endpoint1 cylinder weak factor homotopy replacement provenance
      name endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory model ∧ UnaryHistory object ∧ UnaryHistory endpoint0 ∧
    UnaryHistory endpoint1 ∧ UnaryHistory cylinder ∧ UnaryHistory weak ∧
      UnaryHistory factor ∧ UnaryHistory homotopy ∧ UnaryHistory replacement ∧
        UnaryHistory provenance ∧ UnaryHistory name ∧
          Cont endpoint0 endpoint1 cylinder ∧ Cont cylinder weak factor ∧
            Cont factor homotopy endpoint ∧ PkgSig bundle endpoint pkg

end BEDC.Derived.CylinderObjectUp
