import BEDC.Derived.FiniteTailFilterUp

namespace BEDC.Derived.FiniteTailFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteTailFilterCarrier_sibling_tail_handoff
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N sealRow siblingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N →
      Cont Q E sealRow →
        Cont sealRow C siblingRead →
          PkgSig bundle siblingRead pkg →
            UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory B ∧
              UnaryHistory Q ∧ UnaryHistory E ∧ UnaryHistory sealRow ∧
                UnaryHistory siblingRead ∧ Cont S D R ∧ Cont R B Q ∧
                  Cont Q E sealRow ∧ Cont sealRow C siblingRead ∧ hsame N E ∧
                    PkgSig bundle siblingRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sealRoute siblingRoute siblingPkg
  obtain ⟨unaryS, unaryD, unaryB, unaryE, _unaryH, unaryC, routeR, routeQ,
    sameNameSeal⟩ :=
    carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryS unaryD routeR
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryR unaryB routeQ
  have unarySeal : UnaryHistory sealRow :=
    unary_cont_closed unaryQ unaryE sealRoute
  have unarySibling : UnaryHistory siblingRead :=
    unary_cont_closed unarySeal unaryC siblingRoute
  exact
    ⟨unaryS, unaryD, unaryR, unaryB, unaryQ, unaryE, unarySeal, unarySibling,
      routeR, routeQ, sealRoute, siblingRoute, sameNameSeal, siblingPkg⟩

theorem FinitetailfilterCofinalWindowBudgetNormalForm
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N sealRow realWindowRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N →
      Cont Q E sealRow →
        Cont sealRow H realWindowRead →
          UnaryHistory C →
            Cont realWindowRead C completionRead →
              PkgSig bundle completionRead pkg →
                UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory B ∧
                  UnaryHistory Q ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
                    UnaryHistory sealRow ∧ UnaryHistory realWindowRead ∧
                      UnaryHistory completionRead ∧ Cont S D R ∧ Cont R B Q ∧
                        Cont Q E sealRow ∧ Cont sealRow H realWindowRead ∧
                          Cont realWindowRead C completionRead ∧ hsame N E ∧
                            PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sealRoute realWindowRoute unaryC completionRoute completionPkg
  obtain ⟨unaryS, unaryD, unaryB, unaryE, unaryH, _unaryCarrierC, routeR, routeQ,
    sameNameSeal⟩ :=
    carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryS unaryD routeR
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryR unaryB routeQ
  have unarySeal : UnaryHistory sealRow :=
    unary_cont_closed unaryQ unaryE sealRoute
  have unaryRealWindow : UnaryHistory realWindowRead :=
    unary_cont_closed unarySeal unaryH realWindowRoute
  have unaryCompletion : UnaryHistory completionRead :=
    unary_cont_closed unaryRealWindow unaryC completionRoute
  exact
    ⟨unaryS, unaryD, unaryR, unaryB, unaryQ, unaryE, unaryH, unaryC, unarySeal,
      unaryRealWindow, unaryCompletion, routeR, routeQ, sealRoute, realWindowRoute,
      completionRoute, sameNameSeal, completionPkg⟩

end BEDC.Derived.FiniteTailFilterUp
