import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceHitMissClassifier [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M hit miss hitMiss : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ->
      Cont D0 R hit ->
        Cont D1 R miss ->
          Cont hit miss hitMiss ->
            PkgSig bundle hitMiss pkg ->
              UnaryHistory hit ∧ UnaryHistory miss ∧ UnaryHistory hitMiss ∧
                hsame hitMiss (append hit miss) ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle hitMiss pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame UnaryHistory
  intro carrier hitRoute missRoute hitMissRoute hitMissPkg
  obtain ⟨_xUnary, _k0Unary, _k1Unary, _n0Unary, _n1Unary, d0Unary, d1Unary,
    rUnary, _hsUnary, _cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have hitUnary : UnaryHistory hit :=
    unary_cont_closed d0Unary rUnary hitRoute
  have missUnary : UnaryHistory miss :=
    unary_cont_closed d1Unary rUnary missRoute
  have hitMissUnary : UnaryHistory hitMiss :=
    unary_cont_closed hitUnary missUnary hitMissRoute
  exact
    ⟨hitUnary, missUnary, hitMissUnary, hitMissRoute, provenancePkg, hitMissPkg⟩

end BEDC.Derived.HyperspaceUp
