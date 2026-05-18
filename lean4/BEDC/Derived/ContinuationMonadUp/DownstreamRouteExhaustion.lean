import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_downstream_route_exhaustion [AskSetup] [PackageSetup]
    {A B C f g u H K L N unitRead bindRead categoryRead downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont u f unitRead ->
        Cont K N bindRead ->
          Cont L N categoryRead ->
            Cont categoryRead bindRead downstream ->
              PkgSig bundle downstream pkg ->
                UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
                  UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                    UnaryHistory unitRead ∧ UnaryHistory bindRead ∧
                      UnaryHistory categoryRead ∧ UnaryHistory downstream ∧
                        Cont A f B ∧ Cont B g C ∧ Cont f g K ∧ Cont K u L ∧
                          Cont u f unitRead ∧ Cont K N bindRead ∧ Cont L N categoryRead ∧
                            Cont categoryRead bindRead downstream ∧ hsame N L ∧
                              PkgSig bundle downstream pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier unitRoute bindRoute categoryRoute downstreamRoute downstreamPkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have unaryB : UnaryHistory B := unary_cont_closed unaryA unaryF routeB
  have unaryC : UnaryHistory C := unary_cont_closed unaryB unaryG routeC
  have unaryK : UnaryHistory K := unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L := unary_cont_closed unaryK unaryU routeL
  have unaryN : UnaryHistory N := unary_transport unaryL (hsame_symm sameEndpoint)
  have unaryUnitRead : UnaryHistory unitRead :=
    unary_cont_closed unaryU unaryF unitRoute
  have unaryBindRead : UnaryHistory bindRead :=
    unary_cont_closed unaryK unaryN bindRoute
  have unaryCategoryRead : UnaryHistory categoryRead :=
    unary_cont_closed unaryL unaryN categoryRoute
  have unaryDownstream : UnaryHistory downstream :=
    unary_cont_closed unaryCategoryRead unaryBindRead downstreamRoute
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryUnitRead,
      unaryBindRead, unaryCategoryRead, unaryDownstream, routeB, routeC, routeK, routeL,
        unitRoute, bindRoute, categoryRoute, downstreamRoute, sameEndpoint, downstreamPkg⟩

end BEDC.Derived.ContinuationMonadUp
