import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_verdict_transport_separation
    [AskSetup] [PackageSetup]
    {e a t v h c p n transportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont t h transportRead ->
        PkgSig bundle transportRead pkg ->
          UnaryHistory a ∧ UnaryHistory v ∧ UnaryHistory t ∧
            UnaryHistory transportRead ∧ Cont e a v ∧ Cont t h transportRead ∧
              PkgSig bundle p pkg ∧ PkgSig bundle transportRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier tHTransport transportPkg
  obtain ⟨_eUnary, aUnary, tUnary, vUnary, hUnary, _cUnary, _pUnary, _nUnary,
    eAV, _eTH, _hCN, pPkg, _nPkg, hN⟩ := carrier
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed tUnary hUnary tHTransport
  exact
    ⟨aUnary, vUnary, tUnary, transportUnary, eAV, tHTransport, pPkg, transportPkg, hN⟩

end BEDC.Derived.QuotientSoundnessBoundaryUp
