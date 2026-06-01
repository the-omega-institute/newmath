import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceFiniteCoverLedger [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M subsetRead netRead finiteCoverRead
      directedRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ->
      Cont K0 K1 subsetRead ->
        Cont N0 N1 netRead ->
          Cont subsetRead netRead finiteCoverRead ->
            Cont D0 D1 directedRead ->
              Cont finiteCoverRead directedRead publicRead ->
                PkgSig bundle publicRead pkg ->
                  UnaryHistory subsetRead ∧ UnaryHistory netRead ∧
                    UnaryHistory finiteCoverRead ∧ UnaryHistory directedRead ∧
                      UnaryHistory publicRead ∧ Cont subsetRead netRead finiteCoverRead ∧
                        Cont D0 D1 directedRead ∧
                          Cont finiteCoverRead directedRead publicRead ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist HyperspaceCarrier Cont ProbeBundle PkgSig UnaryHistory
  intro carrier subsetRoute netRoute finiteCoverRoute directedRoute publicRoute publicPkg
  obtain ⟨_xUnary, k0Unary, k1Unary, n0Unary, n1Unary, d0Unary, d1Unary, _rUnary,
    _hsUnary, _cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have subsetUnary : UnaryHistory subsetRead :=
    unary_cont_closed k0Unary k1Unary subsetRoute
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed n0Unary n1Unary netRoute
  have finiteCoverUnary : UnaryHistory finiteCoverRead :=
    unary_cont_closed subsetUnary netUnary finiteCoverRoute
  have directedUnary : UnaryHistory directedRead :=
    unary_cont_closed d0Unary d1Unary directedRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed finiteCoverUnary directedUnary publicRoute
  exact
    ⟨subsetUnary, netUnary, finiteCoverUnary, directedUnary, publicUnary,
      finiteCoverRoute, directedRoute, publicRoute, provenancePkg, publicPkg⟩

end BEDC.Derived.HyperspaceUp
