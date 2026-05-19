import BEDC.Derived.RealWindowSynchronizerUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealWindowSynchronizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealWindowSynchronizerCarrier [AskSetup] [PackageSetup]
    (W R T L S H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame
  UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory T ∧ UnaryHistory L ∧
    UnaryHistory S ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont W R T ∧ hsame N S

theorem RealWindowSynchronizerCarrier_budget_pullback [AskSetup] [PackageSetup]
    {W R T L S H C P N limitRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealWindowSynchronizerCarrier W R T L S H C P N →
      Cont T L limitRead →
        Cont limitRead S realRead →
          PkgSig bundle realRead pkg →
            UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory T ∧ UnaryHistory L ∧
              UnaryHistory S ∧ UnaryHistory limitRead ∧ UnaryHistory realRead ∧
                Cont W R T ∧ Cont T L limitRead ∧ Cont limitRead S realRead ∧
                  hsame N S ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig hsame
  intro carrier contTLLimit contLimitSReal pkgReal
  obtain ⟨unaryW, unaryR, unaryT, unaryL, unaryS, _unaryH, _unaryC, _unaryP,
    _unaryN, contWRT, sameNS⟩ := carrier
  have unaryLimit : UnaryHistory limitRead :=
    unary_cont_closed unaryT unaryL contTLLimit
  have unaryReal : UnaryHistory realRead :=
    unary_cont_closed unaryLimit unaryS contLimitSReal
  exact ⟨unaryW, unaryR, unaryT, unaryL, unaryS, unaryLimit, unaryReal, contWRT,
    contTLLimit, contLimitSReal, sameNS, pkgReal⟩

end BEDC.Derived.RealWindowSynchronizerUp
