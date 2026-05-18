import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_generator_boundary_refusal [AskSetup] [PackageSetup]
    {A B C f g u H K L N category generator boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N category ->
        Cont category N generator ->
          Cont generator N boundary ->
            PkgSig bundle boundary pkg ->
              UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory K ∧
                UnaryHistory L ∧ UnaryHistory N ∧ UnaryHistory category ∧
                  UnaryHistory generator ∧ UnaryHistory boundary ∧ Cont A f B ∧
                    Cont B g C ∧ Cont f g K ∧ Cont K u L ∧ Cont L N category ∧
                      Cont category N generator ∧ Cont generator N boundary ∧
                        hsame N L ∧ PkgSig bundle boundary pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier categoryRoute generatorRoute boundaryRoute boundaryPkg
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
  have unaryBoundary : UnaryHistory boundary :=
    unary_cont_closed unaryGenerator unaryN boundaryRoute
  exact
    ⟨unaryA, unaryB, unaryC, unaryK, unaryL, unaryN, unaryCategory, unaryGenerator,
      unaryBoundary, routeB, routeC, routeK, routeL, categoryRoute, generatorRoute,
      boundaryRoute, sameEndpoint, boundaryPkg⟩

end BEDC.Derived.ContinuationMonadUp
