import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HyperspaceFiniteWindowCarrier [AskSetup] [PackageSetup]
    (X K0 K1 N0 N1 D0 D1 R Hs C P M finiteWindowRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ∧
    Cont D0 R finiteWindowRead ∧ PkgSig bundle finiteWindowRead pkg

theorem HyperspaceFiniteWindowCarrier_readback [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M finiteWindowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceFiniteWindowCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M
        finiteWindowRead bundle pkg →
      UnaryHistory finiteWindowRead ∧ PkgSig bundle P pkg ∧
        PkgSig bundle finiteWindowRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro windowCarrier
  obtain ⟨carrier, finiteWindowRoute, finiteWindowPkg⟩ := windowCarrier
  obtain ⟨_xUnary, _k0Unary, _k1Unary, _n0Unary, _n1Unary, d0Unary, _d1Unary,
    rUnary, _hsUnary, _cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have finiteWindowUnary : UnaryHistory finiteWindowRead :=
    unary_cont_closed d0Unary rUnary finiteWindowRoute
  exact ⟨finiteWindowUnary, provenancePkg, finiteWindowPkg⟩

end BEDC.Derived.HyperspaceUp
