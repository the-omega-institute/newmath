import BEDC.Derived.FiniteTailFilterUp

namespace BEDC.Derived.FiniteTailFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteTailFilterCarrier_formal_target_consumer_route
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N sealRow realWindowRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N ->
      Cont Q E sealRow ->
        Cont sealRow H realWindowRead ->
          Cont realWindowRead C terminalRead ->
            UnaryHistory C ->
              PkgSig bundle terminalRead pkg ->
                UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory B ∧
                  UnaryHistory Q ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
                    UnaryHistory sealRow ∧ UnaryHistory realWindowRead ∧
                      UnaryHistory terminalRead ∧ Cont S D R ∧ Cont R B Q ∧
                        Cont Q E sealRow ∧ Cont sealRow H realWindowRead ∧
                          Cont realWindowRead C terminalRead ∧ hsame N E ∧
                            PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier sealRoute realWindowRoute terminalRoute unaryC terminalPkg
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
  have unaryTerminal : UnaryHistory terminalRead :=
    unary_cont_closed unaryRealWindow unaryC terminalRoute
  exact
    ⟨unaryS, unaryD, unaryR, unaryB, unaryQ, unaryE, unaryH, unaryC, unarySeal,
      unaryRealWindow, unaryTerminal, routeR, routeQ, sealRoute, realWindowRoute,
      terminalRoute, sameNameSeal, terminalPkg⟩

end BEDC.Derived.FiniteTailFilterUp
