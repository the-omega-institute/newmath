import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_route_row_grounding [AskSetup] [PackageSetup]
    {A B C f g u H K L N routeRead grounded : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont K L routeRead ->
        Cont routeRead N grounded ->
          PkgSig bundle grounded pkg ->
            UnaryHistory A /\ UnaryHistory B /\ UnaryHistory C /\ UnaryHistory f /\
              UnaryHistory g /\ UnaryHistory u /\ UnaryHistory K /\ UnaryHistory L /\
                UnaryHistory N /\ UnaryHistory routeRead /\ UnaryHistory grounded /\
                  Cont A f B /\ Cont B g C /\ Cont f g K /\ Cont K u L /\
                    Cont K L routeRead /\ Cont routeRead N grounded /\ hsame N L /\
                      PkgSig bundle grounded pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle PkgSig
  intro carrier routeRow groundedRow groundedPkg
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
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed unaryK unaryL routeRow
  have groundedUnary : UnaryHistory grounded :=
    unary_cont_closed routeReadUnary unaryN groundedRow
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryN,
      routeReadUnary, groundedUnary, routeB, routeC, routeK, routeL, routeRow,
      groundedRow, sameEndpoint, groundedPkg⟩

end BEDC.Derived.ContinuationMonadUp
