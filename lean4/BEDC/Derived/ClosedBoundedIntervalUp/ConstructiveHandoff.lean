import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_constructive_handoff [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported netRouteRead nestedRead coverRead modulusRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont dyadic stream netRouteRead ->
        Cont netRouteRead readback nestedRead ->
          Cont dyadic sealRow coverRead ->
            Cont coverRead provenance modulusRead ->
              Cont nestedRead localName consumerRead ->
                PkgSig bundle consumerRead pkg ->
                  UnaryHistory netRouteRead ∧ UnaryHistory nestedRead ∧
                    UnaryHistory coverRead ∧ UnaryHistory modulusRead ∧
                      UnaryHistory consumerRead ∧ Cont dyadic stream netRouteRead ∧
                        Cont netRouteRead readback nestedRead ∧
                          Cont dyadic sealRow coverRead ∧
                            Cont coverRead provenance modulusRead ∧
                              Cont nestedRead localName consumerRead ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet netRoute nestedRoute coverRoute modulusRoute consumerRoute consumerPkg
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _rationalUnary, dyadicUnary,
    streamUnary, readbackUnary, sealRowUnary, _transportUnary, _replayUnary,
    provenanceUnary, localNameUnary, _exportedUnary, _endpointRoute, _containmentRoute,
    _sealRowRoute, _replayRoute, _nameRoute, provenancePkg, _localNamePkg⟩ := packet
  have netUnary : UnaryHistory netRouteRead :=
    unary_cont_closed dyadicUnary streamUnary netRoute
  have nestedUnary : UnaryHistory nestedRead :=
    unary_cont_closed netUnary readbackUnary nestedRoute
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed dyadicUnary sealRowUnary coverRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed coverUnary provenanceUnary modulusRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed nestedUnary localNameUnary consumerRoute
  exact
    ⟨netUnary, nestedUnary, coverUnary, modulusUnary, consumerUnary, netRoute,
      nestedRoute, coverRoute, modulusRoute, consumerRoute, provenancePkg, consumerPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
