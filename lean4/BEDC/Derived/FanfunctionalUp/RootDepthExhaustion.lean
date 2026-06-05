import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalRootDepthExhaustion [AskSetup] [PackageSetup]
    {C F eps B D W M H K P N barRead depthRead witnessRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface C F eps B D W M H K P N bundle pkg ->
      Cont B D barRead ->
        Cont barRead W depthRead ->
          Cont depthRead F witnessRead ->
            PkgSig bundle witnessRead pkg ->
              UnaryHistory B ∧ UnaryHistory D ∧ UnaryHistory barRead ∧
                UnaryHistory depthRead ∧ UnaryHistory witnessRead ∧
                  Cont B D barRead ∧ Cont barRead W depthRead ∧
                    Cont depthRead F witnessRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle witnessRead pkg := by
  -- BEDC touchpoint anchor: FanFunctionalCarrierSurface BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier barDepth depthWitness witnessReadRoute witnessPkg
  obtain ⟨_cUnary, fUnary, _epsUnary, bUnary, dUnary, wUnary, _mUnary, _hUnary,
    _kUnary, _pUnary, _nUnary, _sameHN, _carrierBarDepth, _carrierWitnessReplay,
    provenancePkg⟩ := carrier
  have barReadUnary : UnaryHistory barRead :=
    unary_cont_closed bUnary dUnary barDepth
  have depthReadUnary : UnaryHistory depthRead :=
    unary_cont_closed barReadUnary wUnary depthWitness
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed depthReadUnary fUnary witnessReadRoute
  exact
    ⟨bUnary, dUnary, barReadUnary, depthReadUnary, witnessReadUnary, barDepth, depthWitness,
      witnessReadRoute, provenancePkg, witnessPkg⟩

end BEDC.Derived.FanfunctionalUp
