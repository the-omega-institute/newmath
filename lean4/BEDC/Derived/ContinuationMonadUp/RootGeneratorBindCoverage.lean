import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_root_generator_bind_coverage
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N unitRead bindRead generator : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont u f unitRead ->
        Cont K N bindRead ->
          Cont bindRead N generator ->
            PkgSig bundle generator pkg ->
              UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
                UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                  UnaryHistory unitRead ∧ UnaryHistory bindRead ∧ UnaryHistory generator ∧
                    Cont A f B ∧ Cont B g C ∧ Cont f g K ∧ Cont K u L ∧
                      Cont u f unitRead ∧ Cont K N bindRead ∧
                        Cont bindRead N generator ∧ hsame N L ∧
                          PkgSig bundle generator pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier unitRoute bindRoute generatorRoute generatorPkg
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
  have unaryUnitRead : UnaryHistory unitRead :=
    unary_cont_closed unaryU unaryF unitRoute
  have unaryBindRead : UnaryHistory bindRead :=
    unary_cont_closed unaryK unaryN bindRoute
  have unaryGenerator : UnaryHistory generator :=
    unary_cont_closed unaryBindRead unaryN generatorRoute
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL,
      unaryUnitRead, unaryBindRead, unaryGenerator, routeB, routeC, routeK, routeL,
      unitRoute, bindRoute, generatorRoute, sameEndpoint, generatorPkg⟩

end BEDC.Derived.ContinuationMonadUp
