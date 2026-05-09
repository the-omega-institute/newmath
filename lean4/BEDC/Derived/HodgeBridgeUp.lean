import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.HodgeBridgeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HodgeBridgeBHistSourcePacket [AskSetup] [PackageSetup]
    (derham cohomology projector bidegree lefschetz contReadback transport endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory derham ∧ UnaryHistory cohomology ∧ UnaryHistory projector ∧
    UnaryHistory bidegree ∧ UnaryHistory lefschetz ∧ UnaryHistory transport ∧
      Cont derham projector bidegree ∧ Cont bidegree lefschetz contReadback ∧
        Cont contReadback cohomology endpoint ∧ PkgSig bundle endpoint pkg

end BEDC.Derived.HodgeBridgeUp
