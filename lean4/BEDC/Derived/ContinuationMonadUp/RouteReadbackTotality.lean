import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_route_readback_totality
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N unitRead firstRead secondRead compositeRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N →
      Cont u N unitRead →
        Cont A f firstRead →
          Cont B g secondRead →
            Cont K L compositeRead →
              Cont unitRead compositeRead publicRead →
                PkgSig bundle publicRead pkg →
                  UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
                    UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                      UnaryHistory unitRead ∧ UnaryHistory firstRead ∧
                        UnaryHistory secondRead ∧ UnaryHistory compositeRead ∧
                          UnaryHistory publicRead ∧ hsame N L ∧
                            PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier unitRoute firstRoute secondRoute compositeRoute publicRoute publicPkg
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
  have unaryFirstRead : UnaryHistory firstRead :=
    unary_cont_closed unaryA unaryF firstRoute
  have unarySecondRead : UnaryHistory secondRead :=
    unary_cont_closed unaryB unaryG secondRoute
  have unaryCompositeRead : UnaryHistory compositeRead :=
    unary_cont_closed unaryK unaryL compositeRoute
  have unaryPublicRead : UnaryHistory publicRead :=
    unary_cont_closed unaryUnitRead unaryCompositeRead publicRoute
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryUnitRead,
      unaryFirstRead, unarySecondRead, unaryCompositeRead, unaryPublicRead,
      sameEndpoint, publicPkg⟩

end BEDC.Derived.ContinuationMonadUp
