import BEDC.Derived.RealPowerSeriesUp

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealPowerSeriesObligationCarrier [AskSetup] [PackageSetup]
    (A R B U T V Q E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory A ∧ UnaryHistory R ∧ UnaryHistory B ∧ UnaryHistory U ∧
    UnaryHistory T ∧ UnaryHistory V ∧ UnaryHistory Q ∧ UnaryHistory E ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        Cont A T Q ∧ Cont R Q U ∧ Cont U V E ∧ PkgSig bundle P pkg

theorem RealPowerSeriesObligationCarrier_radius_obligation [AskSetup] [PackageSetup]
    {A R B U T V Q E H C P N partialRead testRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesObligationCarrier A R B U T V Q E H C P N bundle pkg ->
      Cont A T partialRead ->
        Cont R partialRead testRead ->
          Cont testRead V endpointRead ->
            PkgSig bundle endpointRead pkg ->
              UnaryHistory A ∧ UnaryHistory R ∧ UnaryHistory T ∧ UnaryHistory Q ∧
                UnaryHistory U ∧ UnaryHistory V ∧ UnaryHistory E ∧
                  UnaryHistory partialRead ∧ UnaryHistory testRead ∧
                    UnaryHistory endpointRead ∧ Cont A T partialRead ∧
                      Cont R partialRead testRead ∧ Cont testRead V endpointRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier partialRoute testRoute endpointRoute endpointPkg
  obtain ⟨aUnary, rUnary, _bUnary, uUnary, tUnary, vUnary, qUnary, eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _partialCarrierRoute, _testCarrierRoute,
    _endpointCarrierRoute, pPkg⟩ := carrier
  have partialUnary : UnaryHistory partialRead :=
    unary_cont_closed aUnary tUnary partialRoute
  have testUnary : UnaryHistory testRead :=
    unary_cont_closed rUnary partialUnary testRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed testUnary vUnary endpointRoute
  exact
    ⟨aUnary, rUnary, tUnary, qUnary, uUnary, vUnary, eUnary, partialUnary, testUnary,
      endpointUnary, partialRoute, testRoute, endpointRoute, pPkg, endpointPkg⟩

theorem RealPowerSeriesCarrier_radius_composition [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N A' Z' X' R' W' S' M' E' H' C' P' N'
      radiusRead radiusRead' majorantRead majorantRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      RealPowerSeriesCarrier A' Z' X' R' W' S' M' E' H' C' P' N' bundle pkg ->
        hsame R R' ->
          hsame W W' ->
            hsame S S' ->
              Cont R W radiusRead ->
                Cont R' W' radiusRead' ->
                  Cont radiusRead S majorantRead ->
                    Cont radiusRead' S' majorantRead' ->
                      hsame radiusRead radiusRead' ∧ hsame majorantRead majorantRead' ∧
                        UnaryHistory radiusRead ∧ UnaryHistory majorantRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier carrier' radiusSame windowSame partialSame radiusRoute radiusRoute'
    majorantRoute majorantRoute'
  obtain ⟨_AUnary, _ZUnary, _XUnary, RUnary, WUnary, SUnary, _MUnary, _EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, _coefficientWindow, _radiusMajorant,
    _majorantEndpoint, _pkgSig⟩ := carrier
  obtain ⟨_AUnary', _ZUnary', _XUnary', _RUnary', _WUnary', _SUnary', _MUnary',
    _EUnary', _HUnary', _CUnary', _PUnary', _NUnary', _coefficientWindow',
    _radiusMajorant', _majorantEndpoint', _pkgSig'⟩ := carrier'
  have radiusReadSame : hsame radiusRead radiusRead' :=
    cont_respects_hsame radiusSame windowSame radiusRoute radiusRoute'
  have majorantReadSame : hsame majorantRead majorantRead' :=
    cont_respects_hsame radiusReadSame partialSame majorantRoute majorantRoute'
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed RUnary WUnary radiusRoute
  have majorantReadUnary : UnaryHistory majorantRead :=
    unary_cont_closed radiusReadUnary SUnary majorantRoute
  exact ⟨radiusReadSame, majorantReadSame, radiusReadUnary, majorantReadUnary⟩

end BEDC.Derived.RealPowerSeriesUp
