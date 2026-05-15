import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_real_seal_root_handoff [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n sourceFront selectorFront sealFront : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont m0 u sourceFront →
        Cont sourceFront t selectorFront →
          Cont selectorFront e sealFront →
            PkgSig bundle sealFront pkg →
              UnaryHistory m0 ∧ UnaryHistory m1 ∧ UnaryHistory u ∧ UnaryHistory v ∧
                UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory q ∧ UnaryHistory e ∧
                  UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory p ∧ UnaryHistory n ∧
                    UnaryHistory sourceFront ∧ UnaryHistory selectorFront ∧
                      UnaryHistory sealFront ∧ Cont m0 m1 u ∧ Cont u v t ∧
                        Cont t w q ∧ Cont q e h ∧ Cont m0 u sourceFront ∧
                          Cont sourceFront t selectorFront ∧
                            Cont selectorFront e sealFront ∧ PkgSig bundle p pkg ∧
                              PkgSig bundle sealFront pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame UnaryHistory
  intro carrier sourceRoute selectorRoute sealRoute sealPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have sourceUnary : UnaryHistory sourceFront :=
    unary_cont_closed m0Unary uUnary sourceRoute
  have selectorUnary : UnaryHistory selectorFront :=
    unary_cont_closed sourceUnary tUnary selectorRoute
  have sealUnary : UnaryHistory sealFront :=
    unary_cont_closed selectorUnary eUnary sealRoute
  exact
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary, cUnary,
      pUnary, nUnary, sourceUnary, selectorUnary, sealUnary, m0m1u, uvt, twq, qeh,
      sourceRoute, selectorRoute, sealRoute, pPkg, sealPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
