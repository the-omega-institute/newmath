import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceFiniteHitDirectedCover [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M subsetRead netRead forwardHit reverseHit
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      Cont K0 K1 subsetRead →
        Cont N0 N1 netRead →
          Cont subsetRead D0 forwardHit →
            Cont netRead D1 reverseHit →
              Cont forwardHit reverseHit publicRead →
                PkgSig bundle publicRead pkg →
                  UnaryHistory subsetRead ∧ UnaryHistory netRead ∧
                    UnaryHistory forwardHit ∧ UnaryHistory reverseHit ∧
                      UnaryHistory publicRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier subsetRoute netRoute forwardRoute reverseRoute publicRoute publicPkg
  obtain ⟨_xUnary, k0Unary, k1Unary, n0Unary, n1Unary, d0Unary, d1Unary,
    _rUnary, _hsUnary, _cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have subsetUnary : UnaryHistory subsetRead :=
    unary_cont_closed k0Unary k1Unary subsetRoute
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed n0Unary n1Unary netRoute
  have forwardUnary : UnaryHistory forwardHit :=
    unary_cont_closed subsetUnary d0Unary forwardRoute
  have reverseUnary : UnaryHistory reverseHit :=
    unary_cont_closed netUnary d1Unary reverseRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed forwardUnary reverseUnary publicRoute
  exact
    ⟨subsetUnary, netUnary, forwardUnary, reverseUnary, publicUnary, provenancePkg,
      publicPkg⟩

end BEDC.Derived.HyperspaceUp
