import BEDC.Derived.BishopCompletionModulusUp.TasteGate

namespace BEDC.Derived.BishopCompletionModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopCompletionModulusCarrier_real_seal_ordering [AskSetup] [PackageSetup]
    {M S n k W D R E H C P N sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopCompletionModulusCarrier M S n k W D R E H C P N bundle pkg ->
      Cont R E sealRead ->
        UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory sealRead ∧ Cont M n k ∧
          Cont S k W ∧ Cont W D R ∧ Cont R E sealRead ∧ PkgSig bundle P pkg ∧
            PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier sealRoute
  obtain ⟨_mUnary, _sUnary, _nUnary, _kUnary, _wUnary, _dUnary, rUnary, eUnary,
    _hUnary, _cUnary, _pUnary, _localNameUnary, modulusRoute, windowRoute, handoffRoute,
      _carrierSealRoute, provenancePkg, localNamePkg⟩ := carrier
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed rUnary eUnary sealRoute
  exact
    ⟨rUnary, eUnary, sealUnary, modulusRoute, windowRoute, handoffRoute, sealRoute,
      provenancePkg, localNamePkg⟩

end BEDC.Derived.BishopCompletionModulusUp
