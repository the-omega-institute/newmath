import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HyperspaceFiniteNetCarrier [AskSetup] [PackageSetup]
    (X K0 K1 N0 N1 D0 D1 R Hs C P M : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ∧
    Cont X K0 N0 ∧ Cont X K1 N1 ∧ Cont K1 N1 D0 ∧
      Cont N0 N1 D0 ∧ Cont D0 D1 R

theorem HyperspaceFiniteNetCarrier_closed_rows [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceFiniteNetCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ->
      UnaryHistory N0 ∧ UnaryHistory N1 ∧ UnaryHistory D0 ∧ UnaryHistory R ∧
        Cont X K0 N0 ∧ Cont X K1 N1 ∧ Cont K1 N1 D0 ∧
          Cont N0 N1 D0 ∧ Cont D0 D1 R ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier
  obtain ⟨baseCarrier, sourceLeftRoute, sourceRightRoute, finiteRoute, directedRoute,
    toleranceRoute⟩ := carrier
  obtain ⟨_xUnary, _k0Unary, _k1Unary, n0Unary, n1Unary, d0Unary, _d1Unary,
    rUnary, _hsUnary, _cUnary, _pUnary, _mUnary, provenancePkg⟩ := baseCarrier
  exact
    ⟨n0Unary, n1Unary, d0Unary, rUnary, sourceLeftRoute, sourceRightRoute,
      finiteRoute, directedRoute, toleranceRoute, provenancePkg⟩

end BEDC.Derived.HyperspaceUp
