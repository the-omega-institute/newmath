import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_root_formal_downstream_coverage
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N category generator formal downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N category ->
        Cont category N generator ->
          Cont generator N formal ->
            Cont formal L downstream ->
              PkgSig bundle downstream pkg ->
                UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
                  UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                    UnaryHistory category ∧ UnaryHistory generator ∧ UnaryHistory formal ∧
                      UnaryHistory downstream ∧ Cont A f B ∧ Cont B g C ∧ Cont f g K ∧
                        Cont K u L ∧ Cont L N category ∧ Cont category N generator ∧
                          Cont generator N formal ∧ Cont formal L downstream ∧ hsame N L ∧
                            PkgSig bundle downstream pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier categoryRoute generatorRoute formalRoute downstreamRoute downstreamPkg
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
  have categoryUnary : UnaryHistory category :=
    unary_cont_closed unaryL unaryN categoryRoute
  have generatorUnary : UnaryHistory generator :=
    unary_cont_closed categoryUnary unaryN generatorRoute
  have formalUnary : UnaryHistory formal :=
    unary_cont_closed generatorUnary unaryN formalRoute
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed formalUnary unaryL downstreamRoute
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, categoryUnary,
      generatorUnary, formalUnary, downstreamUnary, routeB, routeC, routeK, routeL,
      categoryRoute, generatorRoute, formalRoute, downstreamRoute, sameEndpoint, downstreamPkg⟩

end BEDC.Derived.ContinuationMonadUp
