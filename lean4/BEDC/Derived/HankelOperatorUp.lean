import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

inductive HankelOperatorUp : Type where
  | carrier

namespace HankelOperatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HankelOperatorCarrier [AskSetup] [PackageSetup]
    (M I A S B H C P N shiftRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory M ∧ UnaryHistory I ∧ UnaryHistory A ∧ UnaryHistory S ∧
    UnaryHistory B ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ UnaryHistory shiftRead ∧ Cont M A shiftRead ∧
        PkgSig bundle P pkg

end HankelOperatorUp

end BEDC.Derived
