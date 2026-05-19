import BEDC.Derived.FiniteTailFilterUp

namespace BEDC.Derived.FiniteTailFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteTailFilterFormalTargetRouteClosure
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N sealRead realWindowRead completionRead terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N →
      Cont Q E sealRead →
        Cont sealRead H realWindowRead →
          UnaryHistory C →
            Cont realWindowRead C completionRead →
              Cont completionRead N terminal →
                PkgSig bundle terminal pkg →
                  UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory B ∧
                    UnaryHistory Q ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
                      UnaryHistory sealRead ∧ UnaryHistory realWindowRead ∧
                        UnaryHistory completionRead ∧ UnaryHistory terminal ∧
                          Cont S D R ∧ Cont R B Q ∧ Cont Q E sealRead ∧
                            Cont sealRead H realWindowRead ∧
                              Cont realWindowRead C completionRead ∧
                                Cont completionRead N terminal ∧ hsame N E ∧
                                  PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sealRoute realWindowRoute unaryC completionRoute terminalRoute terminalPkg
  obtain ⟨unaryS, unaryD, unaryB, unaryE, unaryH, _unaryCarrierC, routeR, routeQ,
    sameNameSeal⟩ := carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryS unaryD routeR
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryR unaryB routeQ
  have unarySeal : UnaryHistory sealRead :=
    unary_cont_closed unaryQ unaryE sealRoute
  have unaryRealWindow : UnaryHistory realWindowRead :=
    unary_cont_closed unarySeal unaryH realWindowRoute
  have unaryCompletion : UnaryHistory completionRead :=
    unary_cont_closed unaryRealWindow unaryC completionRoute
  have unaryN : UnaryHistory N :=
    unary_transport unaryE (hsame_symm sameNameSeal)
  have unaryTerminal : UnaryHistory terminal :=
    unary_cont_closed unaryCompletion unaryN terminalRoute
  exact
    ⟨unaryS, unaryD, unaryR, unaryB, unaryQ, unaryE, unaryH, unaryC, unarySeal,
      unaryRealWindow, unaryCompletion, unaryTerminal, routeR, routeQ, sealRoute,
      realWindowRoute, completionRoute, terminalRoute, sameNameSeal, terminalPkg⟩

end BEDC.Derived.FiniteTailFilterUp
