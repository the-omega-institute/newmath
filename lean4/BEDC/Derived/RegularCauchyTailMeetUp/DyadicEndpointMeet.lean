import BEDC.Derived.RegularCauchyTailMeetUp

namespace BEDC.Derived.RegularCauchyTailMeetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailMeetPacket_dyadic_endpoint_meet [AskSetup] [PackageSetup]
    {r0 r1 w0 w1 m0 m1 tau q h c l n endpoint leftRead rightRead meetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailMeetPacket r0 r1 w0 w1 m0 m1 tau q h c l n bundle pkg ->
      Cont tau q endpoint ->
        Cont r0 endpoint leftRead ->
          Cont r1 endpoint rightRead ->
            Cont leftRead rightRead meetRead ->
              PkgSig bundle meetRead pkg ->
                UnaryHistory endpoint ∧ UnaryHistory leftRead ∧ UnaryHistory rightRead ∧
                  UnaryHistory meetRead ∧ hsame l endpoint ∧ Cont tau q endpoint ∧
                    Cont r0 endpoint leftRead ∧ Cont r1 endpoint rightRead ∧
                      Cont leftRead rightRead meetRead ∧ PkgSig bundle l pkg ∧
                        PkgSig bundle meetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet endpointRoute leftRoute rightRoute meetRoute meetPkg
  obtain ⟨r0Unary, r1Unary, _w0Unary, _w1Unary, _m0Unary, _m1Unary, tauUnary,
    qUnary, _hUnary, _cUnary, _lUnary, _nUnary, _r0w0Row, _r1w1Row, _m0m1Row,
    tauqRow, pkgRow⟩ := packet
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed tauUnary qUnary endpointRoute
  have leftUnary : UnaryHistory leftRead :=
    unary_cont_closed r0Unary endpointUnary leftRoute
  have rightUnary : UnaryHistory rightRead :=
    unary_cont_closed r1Unary endpointUnary rightRoute
  have meetUnary : UnaryHistory meetRead :=
    unary_cont_closed leftUnary rightUnary meetRoute
  have sameEndpoint : hsame l endpoint :=
    cont_respects_hsame (hsame_refl tau) (hsame_refl q) tauqRow endpointRoute
  exact
    ⟨endpointUnary, leftUnary, rightUnary, meetUnary, sameEndpoint, endpointRoute,
      leftRoute, rightRoute, meetRoute, pkgRow, meetPkg⟩

end BEDC.Derived.RegularCauchyTailMeetUp
