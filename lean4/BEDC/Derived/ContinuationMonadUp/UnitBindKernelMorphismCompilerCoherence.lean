import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_unit_bind_kernelmorphism_compiler_coherence
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N unitRead bindRead compiler : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont u f unitRead ->
        Cont K N bindRead ->
          Cont bindRead N compiler ->
            PkgSig bundle compiler pkg ->
              UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
                UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                  UnaryHistory unitRead ∧ UnaryHistory bindRead ∧
                    UnaryHistory compiler ∧ Cont A f B ∧ Cont B g C ∧
                      Cont f g K ∧ Cont K u L ∧ Cont u f unitRead ∧
                        Cont K N bindRead ∧ Cont bindRead N compiler ∧ hsame N L ∧
                          PkgSig bundle compiler pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier unitRoute bindRoute compilerRoute compilerPkg
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
  have unaryCompiler : UnaryHistory compiler :=
    unary_cont_closed unaryBindRead unaryN compilerRoute
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryUnitRead,
      unaryBindRead, unaryCompiler, routeB, routeC, routeK, routeL, unitRoute,
      bindRoute, compilerRoute, sameEndpoint, compilerPkg⟩

end BEDC.Derived.ContinuationMonadUp
