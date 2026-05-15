import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_real_seal_refusal [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n sealRead refused : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont q e sealRead →
        Cont sealRead h refused →
          PkgSig bundle refused pkg →
            UnaryHistory m0 ∧ UnaryHistory m1 ∧ UnaryHistory u ∧ UnaryHistory v ∧
              UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory q ∧ UnaryHistory e ∧
                UnaryHistory sealRead ∧ UnaryHistory refused ∧ Cont m0 m1 u ∧
                  Cont u v t ∧ Cont t w q ∧ Cont q e sealRead ∧
                    Cont sealRead h refused ∧ PkgSig bundle p pkg ∧
                      PkgSig bundle refused pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame
  intro carrier qSeal sealRefused refusedPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      _cUnary, _pUnary, _nUnary, m0m1u, uvt, twq, _qeh, pPkg, hn⟩
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed qUnary eUnary qSeal
  have refusedUnary : UnaryHistory refused :=
    unary_cont_closed sealReadUnary hUnary sealRefused
  exact
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, sealReadUnary,
      refusedUnary, m0m1u, uvt, twq, qSeal, sealRefused, pPkg, refusedPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
