import BEDC.Derived.CategoryUp
import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.Derived.CategoryUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_category_hom_carrier_route [AskSetup] [PackageSetup]
    {A B C f g u H K L N homTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      CategoryHomCarrier A C L ->
        CategoryHomCarrier L N homTail ->
          PkgSig bundle homTail pkg ->
            UnaryHistory A ∧ UnaryHistory C ∧ UnaryHistory L ∧ UnaryHistory N ∧
              UnaryHistory homTail ∧ CategoryHomCarrier A C L ∧
                CategoryHomCarrier L N homTail ∧ hsame N L ∧
                  PkgSig bundle homTail pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier homAC homLN homPkg
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
  have unaryHomTail : UnaryHistory homTail :=
    homLN.right.right.left
  exact
    ⟨unaryA, unaryC, unaryL, unaryN, unaryHomTail, homAC, homLN, sameEndpoint, homPkg⟩

end BEDC.Derived.ContinuationMonadUp
