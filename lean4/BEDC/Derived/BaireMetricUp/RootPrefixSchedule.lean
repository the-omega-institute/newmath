import BEDC.Derived.BaireMetricUp.PrefixWindowAdmission

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireMetricRootPrefixSchedule [AskSetup] [PackageSetup]
    {B W D R U S H C P N prefixRead radiusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricCarrier B W D R U S H C P N bundle pkg →
      Cont S B prefixRead →
        Cont prefixRead W radiusRead →
          UnaryHistory S ∧ UnaryHistory B ∧ UnaryHistory W ∧ UnaryHistory D ∧
            UnaryHistory prefixRead ∧ UnaryHistory radiusRead ∧ Cont S B prefixRead ∧
              Cont prefixRead W radiusRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BaireMetricCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier prefixRoute radiusRoute
  obtain ⟨bUnary, wUnary, dUnary, _rUnary, _uUnary, sUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _carrierSBW, _carrierWDR, _carrierRUC, _carrierCNP,
    provenancePkg, _localNamePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed sUnary bUnary prefixRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed prefixUnary wUnary radiusRoute
  exact
    ⟨sUnary, bUnary, wUnary, dUnary, prefixUnary, radiusUnary, prefixRoute,
      radiusRoute, provenancePkg⟩

end BEDC.Derived.BaireMetricUp
