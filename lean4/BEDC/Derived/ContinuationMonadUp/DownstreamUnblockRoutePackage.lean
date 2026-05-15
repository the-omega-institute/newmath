import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_downstream_unblock_route_package
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N category generator unitRead bindRead surface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N category ->
        Cont category N generator ->
          Cont u f unitRead ->
            Cont K N bindRead ->
              Cont generator bindRead surface ->
                PkgSig bundle surface pkg ->
                  UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
                    UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                      UnaryHistory category ∧ UnaryHistory generator ∧
                        UnaryHistory unitRead ∧ UnaryHistory bindRead ∧
                          UnaryHistory surface ∧ Cont L N category ∧
                            Cont category N generator ∧ Cont u f unitRead ∧
                              Cont K N bindRead ∧ Cont generator bindRead surface ∧
                                hsame N L ∧ PkgSig bundle surface pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier categoryRoute generatorRoute unitRoute bindRoute surfaceRoute surfacePkg
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
  have unaryCategory : UnaryHistory category :=
    unary_cont_closed unaryL unaryN categoryRoute
  have unaryGenerator : UnaryHistory generator :=
    unary_cont_closed unaryCategory unaryN generatorRoute
  have unaryUnitRead : UnaryHistory unitRead :=
    unary_cont_closed unaryU unaryF unitRoute
  have unaryBindRead : UnaryHistory bindRead :=
    unary_cont_closed unaryK unaryN bindRoute
  have unarySurface : UnaryHistory surface :=
    unary_cont_closed unaryGenerator unaryBindRead surfaceRoute
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryCategory,
      unaryGenerator, unaryUnitRead, unaryBindRead, unarySurface, categoryRoute,
      generatorRoute, unitRoute, bindRoute, surfaceRoute, sameEndpoint, surfacePkg⟩

end BEDC.Derived.ContinuationMonadUp
