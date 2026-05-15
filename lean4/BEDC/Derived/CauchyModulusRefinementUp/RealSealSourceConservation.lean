import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementRealSealSourceConservation [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n sourceFront selectorFront sealFront
      referenceSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont m0 u sourceFront ->
        Cont sourceFront t selectorFront ->
          Cont selectorFront e sealFront ->
            Cont q e referenceSeal ->
              hsame selectorFront q ->
                PkgSig bundle sealFront pkg ->
                  PkgSig bundle referenceSeal pkg ->
                    hsame sealFront referenceSeal ∧ UnaryHistory sourceFront ∧
                      UnaryHistory selectorFront ∧ UnaryHistory sealFront ∧
                        UnaryHistory referenceSeal ∧ Cont m0 u sourceFront ∧
                          Cont sourceFront t selectorFront ∧
                            Cont selectorFront e sealFront ∧ Cont q e referenceSeal ∧
                              PkgSig bundle p pkg ∧ PkgSig bundle sealFront pkg ∧
                                PkgSig bundle referenceSeal pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont hsame PkgSig ProbeBundle UnaryHistory
  intro carrier sourceRoute selectorRoute sealRoute referenceRoute sameSelector sealPkg
    referencePkg
  rcases carrier with
    ⟨m0Unary, _m1Unary, uUnary, _vUnary, tUnary, _wUnary, qUnary, eUnary, _hUnary,
      _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, pPkg, hn⟩
  have sourceUnary : UnaryHistory sourceFront :=
    unary_cont_closed m0Unary uUnary sourceRoute
  have selectorUnary : UnaryHistory selectorFront :=
    unary_cont_closed sourceUnary tUnary selectorRoute
  have sealUnary : UnaryHistory sealFront :=
    unary_cont_closed selectorUnary eUnary sealRoute
  have referenceUnary : UnaryHistory referenceSeal :=
    unary_cont_closed qUnary eUnary referenceRoute
  have sameSeal : hsame sealFront referenceSeal :=
    cont_respects_hsame sameSelector (hsame_refl e) sealRoute referenceRoute
  exact
    ⟨sameSeal, sourceUnary, selectorUnary, sealUnary, referenceUnary, sourceRoute,
      selectorRoute, sealRoute, referenceRoute, pPkg, sealPkg, referencePkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
