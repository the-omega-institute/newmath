import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BaireMetricCarrier [AskSetup] [PackageSetup]
    (B W D R U S H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory B ∧ UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory R ∧
    UnaryHistory U ∧ UnaryHistory S ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont S B W ∧ Cont W D R ∧
        Cont R U C ∧ Cont C N P ∧ PkgSig bundle P pkg

theorem BaireMetricCarrier_prefix_window_admission [AskSetup] [PackageSetup]
    {B W D R U S H C P N prefixRead radiusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricCarrier B W D R U S H C P N bundle pkg ->
      Cont S B prefixRead ->
        Cont prefixRead W radiusRead ->
          UnaryHistory prefixRead ∧ UnaryHistory radiusRead ∧ Cont S B prefixRead ∧
            Cont prefixRead W radiusRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BaireMetricCarrier BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier prefixRoute radiusRoute
  obtain ⟨bUnary, wUnary, _dUnary, _rUnary, _uUnary, sUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _carrierSBW, _carrierWDR, _carrierRUC, _carrierCNP,
    carrierPkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed sUnary bUnary prefixRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed prefixUnary wUnary radiusRoute
  exact ⟨prefixUnary, radiusUnary, prefixRoute, radiusRoute, carrierPkg⟩

end BEDC.Derived.BaireMetricUp
