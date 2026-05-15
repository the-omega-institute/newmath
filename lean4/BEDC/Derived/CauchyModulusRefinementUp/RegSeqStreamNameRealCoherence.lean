import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_regseq_streamname_real_coherence
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selectorRead windowRead toleranceRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont v t selectorRead ->
        Cont selectorRead w windowRead ->
          Cont windowRead q toleranceRead ->
            Cont toleranceRead e sealRead ->
              PkgSig bundle sealRead pkg ->
                UnaryHistory m0 ∧ UnaryHistory m1 ∧ UnaryHistory u ∧
                  UnaryHistory v ∧ UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory q ∧
                    UnaryHistory e ∧ UnaryHistory selectorRead ∧
                      UnaryHistory windowRead ∧ UnaryHistory toleranceRead ∧
                        UnaryHistory sealRead ∧ Cont m0 m1 u ∧ Cont u v t ∧
                          Cont v t selectorRead ∧ Cont selectorRead w windowRead ∧
                            Cont windowRead q toleranceRead ∧
                              Cont toleranceRead e sealRead ∧ Cont q e h ∧
                                PkgSig bundle p pkg ∧ PkgSig bundle sealRead pkg ∧
                                  hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro carrier selectorRoute windowRoute toleranceRoute sealRoute sealPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, _hUnary,
      _cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, qeh, pPkg, hn⟩
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed vUnary tUnary selectorRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed selectorUnary wUnary windowRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowUnary qUnary toleranceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary eUnary sealRoute
  exact
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, selectorUnary,
      windowUnary, toleranceUnary, sealUnary, m0m1u, uvt, selectorRoute, windowRoute,
      toleranceRoute, sealRoute, qeh, pPkg, sealPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
