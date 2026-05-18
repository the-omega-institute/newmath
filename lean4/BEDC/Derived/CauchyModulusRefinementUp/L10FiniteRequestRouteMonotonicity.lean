import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementL10FiniteRequestRouteMonotonicity [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n t' w' q' e' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      hsame t t' ->
        hsame w w' ->
          hsame q q' ->
            hsame e e' ->
              Cont u v t' ->
                Cont t' w' q' ->
                  Cont q' e' h ->
                    CauchyModulusRefinementCarrier m0 m1 u v t' w' q' e' h c p n
                        bundle pkg ∧
                      hsame q q' ∧ hsame e e' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sameT sameW sameQ sameE sourceRoute windowRoute sealRoute
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary, cUnary,
      pUnary, nUnary, m0m1u, _uvt, _twq, _qeh, pPkg, sameHN⟩
  have tPrimeUnary : UnaryHistory t' :=
    unary_transport tUnary sameT
  have wPrimeUnary : UnaryHistory w' :=
    unary_transport wUnary sameW
  have qPrimeUnary : UnaryHistory q' :=
    unary_transport qUnary sameQ
  have ePrimeUnary : UnaryHistory e' :=
    unary_transport eUnary sameE
  exact
    ⟨⟨m0Unary, m1Unary, uUnary, vUnary, tPrimeUnary, wPrimeUnary, qPrimeUnary,
        ePrimeUnary, hUnary, cUnary, pUnary, nUnary, m0m1u, sourceRoute, windowRoute,
        sealRoute, pPkg, sameHN⟩,
      sameQ, sameE⟩

end BEDC.Derived.CauchyModulusRefinementUp
