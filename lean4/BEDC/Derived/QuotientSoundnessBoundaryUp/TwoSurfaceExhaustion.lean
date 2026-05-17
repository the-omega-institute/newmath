import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_two_surface_exhaustion [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead transportRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont v t refusalRead ->
        Cont t h transportRead ->
          Cont transportRead n ledgerRead ->
            PkgSig bundle refusalRead pkg ->
              PkgSig bundle transportRead pkg ->
                PkgSig bundle ledgerRead pkg ->
                  UnaryHistory refusalRead ∧ UnaryHistory transportRead ∧
                    UnaryHistory ledgerRead ∧ Cont e a v ∧ Cont e t h ∧
                      Cont v t refusalRead ∧ Cont t h transportRead ∧
                        Cont transportRead n ledgerRead ∧ PkgSig bundle p pkg ∧
                          PkgSig bundle refusalRead pkg ∧
                            PkgSig bundle transportRead pkg ∧
                              PkgSig bundle ledgerRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier vTRefusal tHTransport transportNLedger refusalPkg transportPkg ledgerPkg
  obtain ⟨eUnary, aUnary, tUnary, vUnary, hUnary, _cUnary, _pUnary, nUnary,
    eAV, eTH, _hCN, pPkg, _nPkg, hN⟩ := carrier
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary tUnary vTRefusal
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed tUnary hUnary tHTransport
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed transportUnary nUnary transportNLedger
  exact
    ⟨refusalUnary, transportUnary, ledgerUnary, eAV, eTH, vTRefusal,
      tHTransport, transportNLedger, pPkg, refusalPkg, transportPkg, ledgerPkg, hN⟩

end BEDC.Derived.QuotientSoundnessBoundaryUp
