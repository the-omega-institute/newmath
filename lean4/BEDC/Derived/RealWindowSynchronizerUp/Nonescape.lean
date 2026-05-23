import BEDC.Derived.RealWindowSynchronizerUp.BudgetPullback

namespace BEDC.Derived.RealWindowSynchronizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealWindowSynchronizerCarrier_nonescape [AskSetup] [PackageSetup]
    {W R T L S H C P N routeRead : BHist} :
    RealWindowSynchronizerCarrier W R T L S H C P N →
      Cont S N routeRead →
        UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory T ∧ UnaryHistory L ∧
          UnaryHistory S ∧ UnaryHistory N ∧ UnaryHistory routeRead ∧ Cont W R T ∧
            Cont S N routeRead ∧ hsame N S := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier routeToRead
  obtain ⟨unaryW, unaryR, unaryT, unaryL, unaryS, _unaryH, _unaryC, _unaryP,
    unaryN, contWRT, sameNS⟩ := carrier
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed unaryS unaryN routeToRead
  exact
    ⟨unaryW, unaryR, unaryT, unaryL, unaryS, unaryN, routeReadUnary, contWRT,
      routeToRead, sameNS⟩

end BEDC.Derived.RealWindowSynchronizerUp
