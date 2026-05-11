import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.VectorBundleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def VectorBundleFiniteCarrier [AskSetup] [PackageSetup]
    (bundleSource vecSource trivialization fiberCarrier linearTransition classifierRows
      contRows provenance : BHist)
    (probe : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory bundleSource ∧ UnaryHistory vecSource ∧ UnaryHistory trivialization ∧
    UnaryHistory fiberCarrier ∧ UnaryHistory linearTransition ∧ UnaryHistory classifierRows ∧
      UnaryHistory contRows ∧ UnaryHistory provenance ∧
        Cont bundleSource vecSource trivialization ∧
          Cont trivialization fiberCarrier linearTransition ∧
            Cont linearTransition classifierRows contRows ∧ PkgSig probe provenance pkg

end BEDC.Derived.VectorBundleUp
