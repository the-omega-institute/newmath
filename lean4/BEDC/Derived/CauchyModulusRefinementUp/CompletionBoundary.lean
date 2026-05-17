import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_completion_boundary [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont h c terminal ->
        PkgSig bundle terminal pkg ->
          UnaryHistory m0 ∧ UnaryHistory m1 ∧ UnaryHistory u ∧ UnaryHistory v ∧
            UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory q ∧ UnaryHistory e ∧
              UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory p ∧ UnaryHistory n ∧
                UnaryHistory terminal ∧ Cont m0 m1 u ∧ Cont u v t ∧ Cont t w q ∧
                  Cont q e h ∧ Cont h c terminal ∧ PkgSig bundle p pkg ∧
                    PkgSig bundle terminal pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame UnaryHistory
  intro carrier terminalRoute terminalPkg
  obtain ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
    cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩ := carrier
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed hUnary cUnary terminalRoute
  exact
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, terminalUnary, m0m1u, uvt, twq, qeh, terminalRoute,
      pPkg, terminalPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
