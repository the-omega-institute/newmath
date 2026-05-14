import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_root_consumer_package [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n rootRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont v t rootRead →
        Cont rootRead e sealRead →
          PkgSig bundle sealRead pkg →
            UnaryHistory m0 ∧ UnaryHistory m1 ∧ UnaryHistory u ∧ UnaryHistory v ∧
              UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory q ∧ UnaryHistory e ∧
                UnaryHistory h ∧ UnaryHistory rootRead ∧ UnaryHistory sealRead ∧
                  Cont m0 m1 u ∧ Cont u v t ∧ Cont v t rootRead ∧
                    Cont rootRead e sealRead ∧ Cont q e h ∧ PkgSig bundle p pkg ∧
                      PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier vRootRoute rootSealRoute sealPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      _cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, qeh, pPkg, _hn⟩
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed vUnary tUnary vRootRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed rootUnary eUnary rootSealRoute
  exact
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary, rootUnary,
      sealUnary, m0m1u, uvt, vRootRoute, rootSealRoute, qeh, pPkg, sealPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
