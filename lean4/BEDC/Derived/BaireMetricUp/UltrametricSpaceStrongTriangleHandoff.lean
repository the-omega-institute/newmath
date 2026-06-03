import BEDC.Derived.BaireMetricUp.PrefixWindowAdmission

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireMetricUltrametricSpaceStrongTriangleHandoff [AskSetup] [PackageSetup]
    {B W D R U S H C P N prefixRead radiusRead metricRead parentRead strongRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricCarrier B W D R U S H C P N bundle pkg →
      Cont S B prefixRead →
        Cont prefixRead W radiusRead →
          Cont radiusRead D metricRead →
            Cont metricRead R parentRead →
              Cont parentRead U strongRead →
                PkgSig bundle strongRead pkg →
                  UnaryHistory prefixRead ∧ UnaryHistory radiusRead ∧
                    UnaryHistory metricRead ∧ UnaryHistory parentRead ∧
                      UnaryHistory strongRead ∧ Cont S B prefixRead ∧
                        Cont prefixRead W radiusRead ∧ Cont radiusRead D metricRead ∧
                          Cont metricRead R parentRead ∧ Cont parentRead U strongRead ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle strongRead pkg := by
  -- BEDC touchpoint anchor: BaireMetricCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier prefixRoute radiusRoute metricRoute parentRoute strongRoute strongPkg
  obtain ⟨bUnary, wUnary, dUnary, rUnary, uUnary, sUnary, _hUnary, _cUnary,
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
  have strongUnary : UnaryHistory strongRead :=
    unary_cont_closed parentUnary uUnary strongRoute
  exact
    ⟨prefixUnary, radiusUnary, metricUnary, parentUnary, strongUnary, prefixRoute,
      radiusRoute, metricRoute, parentRoute, strongRoute, provenancePkg, strongPkg⟩

end BEDC.Derived.BaireMetricUp
