import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_bind_route_coverage [AskSetup] [PackageSetup]
    {A B C f g u H K L N bindRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont K N bindRead ->
        PkgSig bundle bindRead pkg ->
          UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
            UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
              UnaryHistory N ∧ UnaryHistory bindRead ∧ Cont A f B ∧ Cont B g C ∧
                Cont f g K ∧ Cont K u L ∧ Cont K N bindRead ∧ hsame N L ∧
                  PkgSig bundle bindRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier bindRoute bindPkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have unaryB : UnaryHistory B := unary_cont_closed unaryA unaryF routeB
  have unaryC : UnaryHistory C := unary_cont_closed unaryB unaryG routeC
  have unaryK : UnaryHistory K := unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L := unary_cont_closed unaryK unaryU routeL
  have unaryN : UnaryHistory N := unary_transport unaryL (hsame_symm sameEndpoint)
  have unaryBindRead : UnaryHistory bindRead := unary_cont_closed unaryK unaryN bindRoute
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryN,
      unaryBindRead, routeB, routeC, routeK, routeL, bindRoute, sameEndpoint, bindPkg⟩

end BEDC.Derived.ContinuationMonadUp
