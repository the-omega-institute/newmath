import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationCarrier_completion_frontier_obligation [AskSetup] [PackageSetup]
    {W M Q T S H C P N frontierRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier W M Q T S H C P N bundle pkg ->
      Cont W M frontierRead ->
        Cont frontierRead Q T ->
          Cont T S sealRead ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory frontierRead ∧ UnaryHistory sealRead ∧ Cont W M frontierRead ∧
                Cont frontierRead Q T ∧ Cont T S sealRead ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier frontierRoute frontierTolerance sealRoute sealPkg
  obtain ⟨wUnary, mUnary, qUnary, _tUnary, sUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    _carrierWMQ, _carrierMQT, _carrierTS, _carrierCN, _carrierPkg⟩ := carrier
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed wUnary mUnary frontierRoute
  have tUnaryFromFrontier : UnaryHistory T :=
    unary_cont_closed frontierUnary qUnary frontierTolerance
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tUnaryFromFrontier sUnary sealRoute
  exact
    ⟨frontierUnary, sealUnary, frontierRoute, frontierTolerance, sealRoute, sealPkg⟩

end BEDC.Derived.CauchyOscillationUp
