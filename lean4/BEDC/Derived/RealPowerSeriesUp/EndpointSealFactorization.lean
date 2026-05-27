import BEDC.Derived.RealPowerSeriesUp

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealPowerSeriesEndpointSealFactorization [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N endpointSeal replay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont E H endpointSeal ->
        Cont endpointSeal C replay ->
          PkgSig bundle replay pkg ->
            UnaryHistory A ∧ UnaryHistory Z ∧ UnaryHistory X ∧ UnaryHistory R ∧
              UnaryHistory W ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory E ∧
                UnaryHistory endpointSeal ∧ UnaryHistory replay ∧ Cont A W S ∧
                  Cont R S M ∧ Cont M E C ∧ Cont E H endpointSeal ∧
                    Cont endpointSeal C replay ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle replay pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier endpointRoute replayRoute replayPkg
  obtain ⟨AUnary, ZUnary, XUnary, RUnary, WUnary, SUnary, MUnary, EUnary,
    HUnary, CUnary, _PUnary, _NUnary, coefficientRoute, radiusRoute,
    endpointCarrierRoute, carrierPkg⟩ := carrier
  have endpointUnary : UnaryHistory endpointSeal :=
    unary_cont_closed EUnary HUnary endpointRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed endpointUnary CUnary replayRoute
  exact
    ⟨AUnary, ZUnary, XUnary, RUnary, WUnary, SUnary, MUnary, EUnary, endpointUnary,
      replayUnary, coefficientRoute, radiusRoute, endpointCarrierRoute, endpointRoute,
      replayRoute, carrierPkg, replayPkg⟩

end BEDC.Derived.RealPowerSeriesUp
