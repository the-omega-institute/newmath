import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_psame_transport_exhaustion [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead transportRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont v t refusalRead ->
        Cont t h transportRead ->
          Cont transportRead n ledgerRead ->
            PkgSig bundle transportRead pkg ->
              PkgSig bundle ledgerRead pkg ->
                UnaryHistory transportRead ∧ UnaryHistory ledgerRead ∧ Cont e t h ∧
                  Cont t h transportRead ∧ Cont transportRead n ledgerRead ∧
                    PkgSig bundle p pkg ∧ PkgSig bundle transportRead pkg ∧
                      PkgSig bundle ledgerRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier _vTRefusal tHTransport transportNLedger transportPkg ledgerPkg
  obtain ⟨_eUnary, _aUnary, tUnary, _vUnary, hUnary, _cUnary, _pUnary, nUnary,
    _eAV, eTH, _hCN, pPkg, _nPkg, hN⟩ := carrier
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed tUnary hUnary tHTransport
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed transportUnary nUnary transportNLedger
  exact
    ⟨transportUnary, ledgerUnary, eTH, tHTransport, transportNLedger, pPkg,
      transportPkg, ledgerPkg, hN⟩

end BEDC.Derived.QuotientSoundnessBoundaryUp
