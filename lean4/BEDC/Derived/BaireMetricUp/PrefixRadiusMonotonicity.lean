import BEDC.Derived.BaireMetricUp.PrefixWindowAdmission

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireMetricCarrier_prefix_radius_monotonicity [AskSetup] [PackageSetup]
    {B W D R U S H C P N prefixRead radiusRead refinedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricCarrier B W D R U S H C P N bundle pkg →
      Cont S B prefixRead →
        Cont prefixRead W radiusRead →
          Cont radiusRead D refinedRead →
            UnaryHistory prefixRead ∧ UnaryHistory radiusRead ∧ UnaryHistory refinedRead ∧
              Cont S B prefixRead ∧ Cont prefixRead W radiusRead ∧
                Cont radiusRead D refinedRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BaireMetricCarrier BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier prefixRoute radiusRoute refinedRoute
  obtain ⟨bUnary, wUnary, dUnary, _rUnary, _uUnary, sUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _carrierSBW, _carrierWDR, _carrierRUC, _carrierCNP,
    carrierPkg, _carrierNamePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed sUnary bUnary prefixRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed prefixUnary wUnary radiusRoute
  have refinedUnary : UnaryHistory refinedRead :=
    unary_cont_closed radiusUnary dUnary refinedRoute
  exact
    ⟨prefixUnary, radiusUnary, refinedUnary, prefixRoute, radiusRoute, refinedRoute,
      carrierPkg⟩

end BEDC.Derived.BaireMetricUp
