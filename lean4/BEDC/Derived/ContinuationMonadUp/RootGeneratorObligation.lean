import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_root_generator_obligation [AskSetup] [PackageSetup]
    {A B C f g u H K L N category generator : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N category ->
        Cont category K generator ->
          PkgSig bundle generator pkg ->
            UnaryHistory u ∧ UnaryHistory f ∧ UnaryHistory g ∧ UnaryHistory K ∧
              UnaryHistory L ∧ UnaryHistory category ∧ UnaryHistory generator ∧
                Cont A f B ∧ Cont B g C ∧ Cont f g K ∧ Cont K u L ∧
                  Cont L N category ∧ Cont category K generator ∧ hsame N L ∧
                    PkgSig bundle generator pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier categoryRoute generatorRoute generatorPkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryK unaryU routeL
  have unaryN : UnaryHistory N :=
    unary_transport unaryL (hsame_symm sameEndpoint)
  have unaryCategory : UnaryHistory category :=
    unary_cont_closed unaryL unaryN categoryRoute
  have unaryGenerator : UnaryHistory generator :=
    unary_cont_closed unaryCategory unaryK generatorRoute
  exact
    ⟨unaryU, unaryF, unaryG, unaryK, unaryL, unaryCategory, unaryGenerator, routeB,
      routeC, routeK, routeL, categoryRoute, generatorRoute, sameEndpoint, generatorPkg⟩

end BEDC.Derived.ContinuationMonadUp
