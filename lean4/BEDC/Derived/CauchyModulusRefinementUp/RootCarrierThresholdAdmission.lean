import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementRootCarrierThresholdAdmission [AskSetup] [PackageSetup]
    {M0 M1 U V T W Q E H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier M0 M1 U V T W Q E H C P N bundle pkg ->
      Cont H C threshold ->
        PkgSig bundle threshold pkg ->
      UnaryHistory M0 ∧ UnaryHistory M1 ∧ UnaryHistory U ∧ UnaryHistory V ∧
        UnaryHistory T ∧ UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory E ∧
          UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
            UnaryHistory threshold ∧
            Cont M0 M1 U ∧ Cont U V T ∧ Cont T W Q ∧ Cont Q E H ∧
              Cont H C threshold ∧ PkgSig bundle P pkg ∧
                PkgSig bundle threshold pkg ∧ hsame H N := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  intro carrier hThreshold thresholdPkg
  obtain
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩ := carrier
  have thresholdUnary : UnaryHistory threshold :=
    unary_cont_closed hUnary cUnary hThreshold
  exact
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, thresholdUnary, m0m1u, uvt, twq, qeh, hThreshold,
      pPkg, thresholdPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
