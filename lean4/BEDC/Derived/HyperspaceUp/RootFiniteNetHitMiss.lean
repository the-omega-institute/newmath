import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceRootFiniteNetHitMiss [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M netLeft netRight hitMissRead replayRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ->
      Cont K0 N0 netLeft ->
        Cont K1 N1 netRight ->
          Cont netLeft netRight hitMissRead ->
            Cont Hs C replayRead ->
              PkgSig bundle hitMissRead pkg ->
                UnaryHistory netLeft ∧ UnaryHistory netRight ∧
                  UnaryHistory hitMissRead ∧ UnaryHistory replayRead ∧
                    Cont K0 N0 netLeft ∧ Cont K1 N1 netRight ∧
                      Cont netLeft netRight hitMissRead ∧ Cont Hs C replayRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle hitMissRead pkg := by
  -- BEDC touchpoint anchor: BHist HyperspaceCarrier Cont ProbeBundle PkgSig UnaryHistory
  intro carrier netLeftRoute netRightRoute hitMissRoute replayRoute hitMissPkg
  obtain ⟨_xUnary, k0Unary, k1Unary, n0Unary, n1Unary, _d0Unary, _d1Unary,
    _rUnary, hsUnary, cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have netLeftUnary : UnaryHistory netLeft :=
    unary_cont_closed k0Unary n0Unary netLeftRoute
  have netRightUnary : UnaryHistory netRight :=
    unary_cont_closed k1Unary n1Unary netRightRoute
  have hitMissUnary : UnaryHistory hitMissRead :=
    unary_cont_closed netLeftUnary netRightUnary hitMissRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed hsUnary cUnary replayRoute
  exact
    ⟨netLeftUnary, netRightUnary, hitMissUnary, replayUnary, netLeftRoute,
      netRightRoute, hitMissRoute, replayRoute, provenancePkg, hitMissPkg⟩

end BEDC.Derived.HyperspaceUp
