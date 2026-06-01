import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceFiniteNetHit [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M subsetRead netRead hitRead toleranceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      Cont K0 K1 subsetRead →
        Cont N0 N1 netRead →
          Cont subsetRead D0 hitRead →
            Cont hitRead R toleranceRead →
              PkgSig bundle toleranceRead pkg →
                UnaryHistory subsetRead ∧ UnaryHistory netRead ∧ UnaryHistory hitRead ∧
                  UnaryHistory toleranceRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle toleranceRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier subsetRoute netRoute hitRoute toleranceRoute tolerancePkg
  obtain ⟨_xUnary, k0Unary, k1Unary, n0Unary, n1Unary, d0Unary, _d1Unary,
    rUnary, _hsUnary, _cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have subsetUnary : UnaryHistory subsetRead :=
    unary_cont_closed k0Unary k1Unary subsetRoute
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed n0Unary n1Unary netRoute
  have hitUnary : UnaryHistory hitRead :=
    unary_cont_closed subsetUnary d0Unary hitRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed hitUnary rUnary toleranceRoute
  exact ⟨subsetUnary, netUnary, hitUnary, toleranceUnary, provenancePkg, tolerancePkg⟩

end BEDC.Derived.HyperspaceUp
