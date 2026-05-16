import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_generator_category_consumer_triad [AskSetup] [PackageSetup]
    {A B C f g u H K L N generatorRead categoryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N generatorRead ->
        Cont generatorRead L categoryRead ->
          PkgSig bundle categoryRead pkg ->
            UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
              UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                UnaryHistory generatorRead ∧ UnaryHistory categoryRead ∧
                  Cont A f B ∧ Cont B g C ∧ Cont f g K ∧ Cont K u L ∧
                    Cont L N generatorRead ∧ Cont generatorRead L categoryRead ∧
                      hsame N L ∧ PkgSig bundle categoryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier generatorRoute categoryRoute pkgSig
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
  have unaryN : UnaryHistory N :=
    unary_transport unaryL (hsame_symm sameEndpoint)
  have unaryGeneratorRead : UnaryHistory generatorRead :=
    unary_cont_closed unaryL unaryN generatorRoute
  have unaryCategoryRead : UnaryHistory categoryRead :=
    unary_cont_closed unaryGeneratorRead unaryL categoryRoute
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL,
      unaryGeneratorRead, unaryCategoryRead, routeB, routeC, routeK, routeL,
      generatorRoute, categoryRoute, sameEndpoint, pkgSig⟩

end BEDC.Derived.ContinuationMonadUp
