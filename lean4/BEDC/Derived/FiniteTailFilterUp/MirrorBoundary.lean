import BEDC.Derived.FiniteTailFilterUp

namespace BEDC.Derived.FiniteTailFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteTailFilterCarrier_left_right_mirror_boundary [AskSetup] [PackageSetup]
    {S D R B Q E H C P N sealRead leftRead rightRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkgL pkgR : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N →
      Cont Q E sealRead →
        Cont sealRead H leftRead →
          Cont sealRead H rightRead →
            PkgSig bundle leftRead pkgL →
              PkgSig bundle rightRead pkgR →
                hsame leftRead rightRead ∧ UnaryHistory leftRead ∧
                  UnaryHistory rightRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier sealRoute leftRoute rightRoute _leftPkg _rightPkg
  obtain ⟨unaryS, unaryD, unaryB, unaryE, unaryH, _unaryC, routeR, routeQ,
    _sameNameSeal⟩ := carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryS unaryD routeR
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryR unaryB routeQ
  have unarySeal : UnaryHistory sealRead :=
    unary_cont_closed unaryQ unaryE sealRoute
  have unaryLeft : UnaryHistory leftRead :=
    unary_cont_closed unarySeal unaryH leftRoute
  have unaryRight : UnaryHistory rightRead :=
    unary_cont_closed unarySeal unaryH rightRoute
  exact ⟨cont_deterministic leftRoute rightRoute, unaryLeft, unaryRight⟩

end BEDC.Derived.FiniteTailFilterUp
