import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceFiniteHausdorffRootObligations [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M subsetRead netRead directedLeft directedRight
      symmetricRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      Cont K0 K1 subsetRead →
        Cont N0 N1 netRead →
          Cont D0 R directedLeft →
            Cont D1 R directedRight →
              Cont directedLeft directedRight symmetricRead →
                PkgSig bundle symmetricRead pkg →
                  UnaryHistory subsetRead ∧ UnaryHistory netRead ∧
                    UnaryHistory directedLeft ∧ UnaryHistory directedRight ∧
                      UnaryHistory symmetricRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle symmetricRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier subsetRoute netRoute directedLeftRoute directedRightRoute symmetricRoute
    symmetricPkg
  obtain ⟨_xUnary, k0Unary, k1Unary, n0Unary, n1Unary, d0Unary, d1Unary, rUnary,
    _hsUnary, _cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have subsetUnary : UnaryHistory subsetRead :=
    unary_cont_closed k0Unary k1Unary subsetRoute
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed n0Unary n1Unary netRoute
  have directedLeftUnary : UnaryHistory directedLeft :=
    unary_cont_closed d0Unary rUnary directedLeftRoute
  have directedRightUnary : UnaryHistory directedRight :=
    unary_cont_closed d1Unary rUnary directedRightRoute
  have symmetricUnary : UnaryHistory symmetricRead :=
    unary_cont_closed directedLeftUnary directedRightUnary symmetricRoute
  exact
    ⟨subsetUnary, netUnary, directedLeftUnary, directedRightUnary, symmetricUnary,
      provenancePkg, symmetricPkg⟩

end BEDC.Derived.HyperspaceUp
