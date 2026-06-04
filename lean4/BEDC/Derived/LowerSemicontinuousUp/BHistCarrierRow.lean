import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LowerSemicontinuousBHistCarrierRow [AskSetup] [PackageSetup]
    (L : LowerSemicontinuousUp) (windowRead epigraphRead locatedRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  match L with
  | LowerSemicontinuousUp.mk X F E W R O _H _C P N =>
      UnaryHistory X ∧ UnaryHistory F ∧ UnaryHistory E ∧ UnaryHistory W ∧
        UnaryHistory R ∧ UnaryHistory O ∧ Cont W R windowRead ∧
          Cont windowRead E epigraphRead ∧ Cont epigraphRead O locatedRead ∧
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg

end BEDC.Derived.LowerSemicontinuousUp
