import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_psame_bridge_handoff [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead transportRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont v t refusalRead ->
        Cont t h transportRead ->
          Cont transportRead n bridgeRead ->
            PkgSig bundle refusalRead pkg ->
              PkgSig bundle transportRead pkg ->
                PkgSig bundle bridgeRead pkg ->
                  UnaryHistory refusalRead ∧ UnaryHistory transportRead ∧
                    UnaryHistory bridgeRead ∧ Cont e a v ∧ Cont e t h ∧
                      Cont v t refusalRead ∧ Cont t h transportRead ∧
                        Cont transportRead n bridgeRead ∧ PkgSig bundle p pkg ∧
                          PkgSig bundle bridgeRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier vTRefusal tHTransport transportNBridge _refusalPkg _transportPkg bridgePkg
  obtain ⟨_eUnary, _aUnary, tUnary, vUnary, hUnary, _cUnary, _pUnary, nUnary, eAV,
    eTH, _hCN, pPkg, _nPkg, hN⟩ := carrier
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary tUnary vTRefusal
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed tUnary hUnary tHTransport
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed transportUnary nUnary transportNBridge
  exact
    ⟨refusalUnary, transportUnary, bridgeUnary, eAV, eTH, vTRefusal, tHTransport,
      transportNBridge, pPkg, bridgePkg, hN⟩

end BEDC.Derived.QuotientSoundnessBoundaryUp
