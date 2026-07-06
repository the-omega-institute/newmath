import BEDC.Derived.FiniteCauchyGluingBudgetUp.TasteGate

namespace BEDC.Derived.FiniteCauchyGluingBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def finiteCauchyGluingBudgetClassifier [AskSetup] [PackageSetup]
    (G L T S K U V D R H C P N candidate : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  hsame candidate N ∧ Cont G L T ∧ Cont T S K ∧ Cont K U D ∧ Cont D V R ∧
    Cont H C P ∧ PkgSig bundle N pkg

end BEDC.Derived.FiniteCauchyGluingBudgetUp
