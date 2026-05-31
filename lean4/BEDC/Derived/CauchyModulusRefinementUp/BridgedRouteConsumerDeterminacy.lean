import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_bridged_route_consumer_determinacy
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n bridgeRead normalRead exactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont w q bridgeRead →
        Cont bridgeRead e normalRead →
          Cont normalRead h exactRead →
            PkgSig bundle exactRead pkg →
              UnaryHistory w ∧ UnaryHistory q ∧ UnaryHistory bridgeRead ∧
                UnaryHistory normalRead ∧ UnaryHistory exactRead ∧ Cont w q bridgeRead ∧
                  Cont bridgeRead e normalRead ∧ Cont normalRead h exactRead ∧
                    PkgSig bundle p pkg ∧ PkgSig bundle exactRead pkg := by
  -- BEDC touchpoint anchor: CauchyModulusRefinementCarrier BHist ProbeBundle Pkg Cont
  intro carrier bridgeRoute normalRoute exactRoute exactPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, wUnary, qUnary, eUnary, hUnary,
      _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, pPkg, _hn⟩
  have bridgeReadUnary : UnaryHistory bridgeRead :=
    unary_cont_closed wUnary qUnary bridgeRoute
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed bridgeReadUnary eUnary normalRoute
  have exactReadUnary : UnaryHistory exactRead :=
    unary_cont_closed normalReadUnary hUnary exactRoute
  exact
    ⟨wUnary, qUnary, bridgeReadUnary, normalReadUnary, exactReadUnary, bridgeRoute,
      normalRoute, exactRoute, pPkg, exactPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
