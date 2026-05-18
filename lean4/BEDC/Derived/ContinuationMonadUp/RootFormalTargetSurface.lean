import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_root_formal_target_surface [AskSetup] [PackageSetup]
    {A B C f g u H K L N category generator formal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N category ->
        Cont category N generator ->
          Cont generator N formal ->
            PkgSig bundle formal pkg ->
              UnaryHistory category ∧ UnaryHistory generator ∧ UnaryHistory formal ∧
                Cont L N category ∧ Cont category N generator ∧ Cont generator N formal ∧
                  hsame N L ∧ PkgSig bundle formal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier categoryRoute generatorRoute formalRoute formalPkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have unaryB : UnaryHistory B :=
    unary_cont_closed unaryA unaryF routeB
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
  exact
    ⟨categoryUnary, generatorUnary, formalUnary, categoryRoute, generatorRoute, formalRoute,
      sameEndpoint, formalPkg⟩

end BEDC.Derived.ContinuationMonadUp
