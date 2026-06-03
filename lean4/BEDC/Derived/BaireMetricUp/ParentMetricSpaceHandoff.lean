import BEDC.Derived.BaireMetricUp.PrefixWindowAdmission

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireMetricCarrier_parent_metricspace_handoff [AskSetup] [PackageSetup]
    {B W D R U S H C P N prefixRead radiusRead metricRead parentRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricCarrier B W D R U S H C P N bundle pkg →
      Cont S B prefixRead →
        Cont prefixRead W radiusRead →
          Cont radiusRead D metricRead →
            Cont metricRead R parentRead →
              PkgSig bundle parentRead pkg →
                UnaryHistory prefixRead ∧ UnaryHistory radiusRead ∧
                  UnaryHistory metricRead ∧ UnaryHistory parentRead ∧
                    Cont S B prefixRead ∧ Cont prefixRead W radiusRead ∧
                      Cont radiusRead D metricRead ∧ Cont metricRead R parentRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle parentRead pkg := by
  -- BEDC touchpoint anchor: BaireMetricCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier prefixRoute radiusRoute metricRoute parentRoute parentPkg
  obtain ⟨bUnary, wUnary, dUnary, rUnary, _uUnary, sUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _carrierSBW, _carrierWDR, _carrierRUC, _carrierCNP,
    provenancePkg, _namePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed sUnary bUnary prefixRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed prefixUnary wUnary radiusRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed radiusUnary dUnary metricRoute
  have parentUnary : UnaryHistory parentRead :=
    unary_cont_closed metricUnary rUnary parentRoute
  exact
    ⟨prefixUnary,
      radiusUnary,
      metricUnary,
      parentUnary,
      prefixRoute,
      radiusRoute,
      metricRoute,
      parentRoute,
      provenancePkg,
      parentPkg⟩

end BEDC.Derived.BaireMetricUp
