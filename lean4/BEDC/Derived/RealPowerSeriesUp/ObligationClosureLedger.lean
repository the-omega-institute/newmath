import BEDC.Derived.RealPowerSeriesUp

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealPowerSeriesCarrier_obligation_closure_ledger [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N coefficientRead radiusRead productRead majorantRead
      endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont A W coefficientRead ->
        Cont A W productRead ->
          Cont R S radiusRead ->
            Cont S M majorantRead ->
              Cont majorantRead E endpointRead ->
                PkgSig bundle productRead pkg ->
                  PkgSig bundle endpointRead pkg ->
                    UnaryHistory A ∧ UnaryHistory Z ∧ UnaryHistory X ∧ UnaryHistory R ∧
                      UnaryHistory W ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory E ∧
                        UnaryHistory C ∧ UnaryHistory coefficientRead ∧
                          UnaryHistory radiusRead ∧ UnaryHistory productRead ∧
                            UnaryHistory majorantRead ∧ UnaryHistory endpointRead ∧
                              Cont A W S ∧ Cont A W coefficientRead ∧
                                Cont A W productRead ∧ Cont R S radiusRead ∧
                                  Cont S M majorantRead ∧
                                    Cont majorantRead E endpointRead ∧ Cont M E C ∧
                                      PkgSig bundle P pkg ∧ PkgSig bundle productRead pkg ∧
                                        PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: RealPowerSeriesCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier coefficientRoute productRoute radiusRoute majorantRoute endpointRoute
    productPkg endpointPkg
  obtain ⟨AUnary, ZUnary, XUnary, RUnary, WUnary, SUnary, MUnary, EUnary, _HUnary,
    CUnary, _PUnary, _NUnary, coefficientWindow, _radiusMajorant, majorantEndpoint,
    pkgSig⟩ := carrier
  have coefficientUnary : UnaryHistory coefficientRead :=
    unary_cont_closed AUnary WUnary coefficientRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed RUnary SUnary radiusRoute
  have productUnary : UnaryHistory productRead :=
    unary_cont_closed AUnary WUnary productRoute
  have majorantUnary : UnaryHistory majorantRead :=
    unary_cont_closed SUnary MUnary majorantRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed majorantUnary EUnary endpointRoute
  exact
    ⟨AUnary, ZUnary, XUnary, RUnary, WUnary, SUnary, MUnary, EUnary, CUnary,
      coefficientUnary, radiusUnary, productUnary, majorantUnary, endpointUnary,
      coefficientWindow, coefficientRoute, productRoute, radiusRoute, majorantRoute,
      endpointRoute, majorantEndpoint, pkgSig, productPkg, endpointPkg⟩

end BEDC.Derived.RealPowerSeriesUp
