import BEDC.Derived.RealPowerSeriesUp

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealPowerSeriesCarrier_root_radius_majorant_triad [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N rootMajorant endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont R W S ->
        Cont S M rootMajorant ->
          Cont rootMajorant E endpointRead ->
            PkgSig bundle endpointRead pkg ->
              UnaryHistory R ∧ UnaryHistory W ∧ UnaryHistory S ∧ UnaryHistory M ∧
                UnaryHistory rootMajorant ∧ UnaryHistory endpointRead ∧
                  Cont R W S ∧ Cont S M rootMajorant ∧
                    Cont rootMajorant E endpointRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier radiusWindow rootRoute endpointRoute endpointPkg
  obtain ⟨_AUnary, _ZUnary, _XUnary, RUnary, WUnary, SUnary, MUnary, EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, _coefficientWindow, _radiusMajorant,
    _majorantEndpoint, carrierPkg⟩ := carrier
  have rootUnary : UnaryHistory rootMajorant :=
    unary_cont_closed SUnary MUnary rootRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed rootUnary EUnary endpointRoute
  exact
    ⟨RUnary, WUnary, SUnary, MUnary, rootUnary, endpointUnary, radiusWindow,
      rootRoute, endpointRoute, carrierPkg, endpointPkg⟩

theorem RealPowerSeriesCarrier_root_unblock_obligation_surface [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N productRead radiusRead majorantRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont A W productRead ->
        Cont R W radiusRead ->
          Cont S M majorantRead ->
            Cont majorantRead E endpointRead ->
              PkgSig bundle endpointRead pkg ->
                UnaryHistory A ∧ UnaryHistory R ∧ UnaryHistory W ∧ UnaryHistory S ∧
                  UnaryHistory M ∧ UnaryHistory E ∧ UnaryHistory productRead ∧
                    UnaryHistory radiusRead ∧ UnaryHistory majorantRead ∧
                      UnaryHistory endpointRead ∧ Cont A W productRead ∧
                        Cont R W radiusRead ∧ Cont S M majorantRead ∧
                          Cont majorantRead E endpointRead ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier productRoute radiusRoute majorantRoute endpointRoute endpointPkg
  obtain ⟨AUnary, _ZUnary, _XUnary, RUnary, WUnary, SUnary, MUnary, EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, _coefficientWindow, _radiusMajorant,
    _majorantEndpoint, carrierPkg⟩ := carrier
  have productUnary : UnaryHistory productRead :=
    unary_cont_closed AUnary WUnary productRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed RUnary WUnary radiusRoute
  have majorantUnary : UnaryHistory majorantRead :=
    unary_cont_closed SUnary MUnary majorantRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed majorantUnary EUnary endpointRoute
  exact
    ⟨AUnary, RUnary, WUnary, SUnary, MUnary, EUnary, productUnary, radiusUnary,
      majorantUnary, endpointUnary, productRoute, radiusRoute, majorantRoute,
      endpointRoute, carrierPkg, endpointPkg⟩

end BEDC.Derived.RealPowerSeriesUp
