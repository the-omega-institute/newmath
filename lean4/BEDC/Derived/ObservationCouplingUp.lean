import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ObservationCouplingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ObservationCouplingCarrier [AskSetup] [PackageSetup]
    (ha hb ra rb H C L P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory ha ∧ UnaryHistory hb ∧ UnaryHistory ra ∧ UnaryHistory rb ∧
    hsame H (append ha hb) ∧ Cont ha ra C ∧ Cont hb rb L ∧ PkgSig bundle P pkg ∧
      hsame N (append C L)

end BEDC.Derived.ObservationCouplingUp
