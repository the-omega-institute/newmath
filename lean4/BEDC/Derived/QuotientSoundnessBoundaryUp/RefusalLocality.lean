import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_refusal_locality [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont e a v ->
        Cont v h refusalRead ->
          PkgSig bundle refusalRead pkg ->
            UnaryHistory a ∧ UnaryHistory v ∧ UnaryHistory refusalRead ∧ Cont e a v ∧
              Cont v h refusalRead ∧ PkgSig bundle refusalRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier eAV vHRefusal refusalPkg
  obtain ⟨eUnary, aUnary, _tUnary, _vUnary, hUnary, _cUnary, _pUnary, _nUnary,
    _carrierEAV, _eTH, _hCN, _pPkg, _nPkg, hN⟩ := carrier
  have vUnary : UnaryHistory v := unary_cont_closed eUnary aUnary eAV
  have refusalUnary : UnaryHistory refusalRead := unary_cont_closed vUnary hUnary vHRefusal
  exact ⟨aUnary, vUnary, refusalUnary, eAV, vHRefusal, refusalPkg, hN⟩

end BEDC.Derived.QuotientSoundnessBoundaryUp
