import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_root_category_hom_consumer_totality
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N categoryRead homRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont K L categoryRead ->
        Cont categoryRead u homRead ->
          PkgSig bundle homRead pkg ->
            UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧
              UnaryHistory f ∧ UnaryHistory g ∧ UnaryHistory u ∧
                UnaryHistory K ∧ UnaryHistory L ∧ UnaryHistory categoryRead ∧
                  UnaryHistory homRead ∧ Cont A f B ∧ Cont B g C ∧
                    Cont f g K ∧ Cont K u L ∧ Cont K L categoryRead ∧
                      Cont categoryRead u homRead ∧ hsame N L ∧
                        PkgSig bundle homRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier categoryRoute homRoute homPkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have unaryB : UnaryHistory B :=
    unary_cont_closed unaryA unaryF routeB
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryB unaryG routeC
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryK unaryU routeL
  have unaryCategoryRead : UnaryHistory categoryRead :=
    unary_cont_closed unaryK unaryL categoryRoute
  have unaryHomRead : UnaryHistory homRead :=
    unary_cont_closed unaryCategoryRead unaryU homRoute
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL,
      unaryCategoryRead, unaryHomRead, routeB, routeC, routeK, routeL, categoryRoute,
      homRoute, sameEndpoint, homPkg⟩

end BEDC.Derived.ContinuationMonadUp
