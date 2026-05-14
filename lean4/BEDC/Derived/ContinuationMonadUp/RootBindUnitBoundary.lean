import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_root_bind_unit_boundary [AskSetup] [PackageSetup]
    {A B C f g u H K L N unitRead bindRead boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont u N unitRead ->
        Cont K L bindRead ->
          Cont unitRead bindRead boundary ->
            PkgSig bundle boundary pkg ->
              UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
                UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                  UnaryHistory N ∧ UnaryHistory unitRead ∧ UnaryHistory bindRead ∧
                    UnaryHistory boundary ∧ Cont A f B ∧ Cont B g C ∧ Cont f g K ∧
                      Cont K u L ∧ Cont u N unitRead ∧ Cont K L bindRead ∧
                        Cont unitRead bindRead boundary ∧ hsame N L ∧
                          PkgSig bundle boundary pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier unitRoute bindRoute boundaryRoute boundaryPkg
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
    unary_cont_closed unaryU unaryN unitRoute
  have unaryBindRead : UnaryHistory bindRead :=
    unary_cont_closed unaryK unaryL bindRoute
  have unaryBoundary : UnaryHistory boundary :=
    unary_cont_closed unaryUnitRead unaryBindRead boundaryRoute
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryN,
      unaryUnitRead, unaryBindRead, unaryBoundary, routeB, routeC, routeK, routeL,
      unitRoute, bindRoute, boundaryRoute, sameEndpoint, boundaryPkg⟩

end BEDC.Derived.ContinuationMonadUp
