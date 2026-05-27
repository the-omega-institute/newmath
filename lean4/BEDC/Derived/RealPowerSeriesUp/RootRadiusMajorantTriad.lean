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

end BEDC.Derived.RealPowerSeriesUp
