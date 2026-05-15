import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_real_seal_source_conservation
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n hSeal routed : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont q e hSeal ->
        Cont hSeal c routed ->
          PkgSig bundle routed pkg ->
            hsame h hSeal ∧ UnaryHistory routed ∧ Cont m0 m1 u ∧ Cont u v t ∧
              Cont q e hSeal ∧ Cont hSeal c routed ∧ PkgSig bundle routed pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  intro carrier hSealRow routedRow routedPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, _wUnary, qUnary, eUnary, hUnary,
      cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, carrierSealRow, _pPkg, _hn⟩
  have sameSeal : hsame h hSeal :=
    cont_respects_hsame (hsame_refl q) (hsame_refl e) carrierSealRow hSealRow
  have hSealUnary : UnaryHistory hSeal :=
    unary_cont_closed qUnary eUnary hSealRow
  have routedUnary : UnaryHistory routed :=
    unary_cont_closed hSealUnary cUnary routedRow
  exact ⟨sameSeal, routedUnary, m0m1u, uvt, hSealRow, routedRow, routedPkg⟩

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
