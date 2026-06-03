import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationCarrier_uniform_criterion_consumer [AskSetup] [PackageSetup]
    {W M Q T S H C P N uniformRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier W M Q T S H C P N bundle pkg ->
      Cont W M uniformRead ->
        Cont uniformRead Q replayRead ->
          PkgSig bundle replayRead pkg ->
            UnaryHistory W ∧ UnaryHistory M ∧ UnaryHistory Q ∧ UnaryHistory T ∧
              UnaryHistory uniformRead ∧ UnaryHistory replayRead ∧ Cont W M uniformRead ∧
                Cont uniformRead Q replayRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier routeWM routeUQ replayPkg
  obtain ⟨wUnary, mUnary, qUnary, tUnary, _sUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    _wmq, _mqt, _tsc, _cnp, carrierPkg⟩ := carrier
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed wUnary mUnary routeWM
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed uniformUnary qUnary routeUQ
  exact
    ⟨wUnary, mUnary, qUnary, tUnary, uniformUnary, replayUnary, routeWM, routeUQ,
      carrierPkg, replayPkg⟩

end BEDC.Derived.CauchyOscillationUp
