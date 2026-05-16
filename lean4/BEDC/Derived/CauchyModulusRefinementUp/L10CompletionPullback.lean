import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_l10_completion_pullback
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n rootFront selected readback sealRead support
      completion : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont m0 u rootFront ->
        Cont t w selected ->
          Cont selected q readback ->
            Cont readback e sealRead ->
              Cont sealRead h support ->
                Cont support c completion ->
                  PkgSig bundle completion pkg ->
                    UnaryHistory rootFront ∧ UnaryHistory selected ∧
                      UnaryHistory readback ∧ UnaryHistory sealRead ∧
                        UnaryHistory support ∧ UnaryHistory completion ∧
                          Cont m0 m1 u ∧ Cont m0 u rootFront ∧ Cont u v t ∧
                            Cont t w selected ∧ Cont selected q readback ∧
                              Cont readback e sealRead ∧ Cont sealRead h support ∧
                                Cont support c completion ∧ PkgSig bundle p pkg ∧
                                  PkgSig bundle completion pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle hsame UnaryHistory
  intro carrier m0URootFront tWSelected selectedQReadback readbackESealRead
    sealReadHSupport supportCCompletion completionPkg
  rcases carrier with
    ⟨m0Unary, _m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, _qeh, pPkg, hn⟩
  have rootFrontUnary : UnaryHistory rootFront :=
    unary_cont_closed m0Unary uUnary m0URootFront
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary tWSelected
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary selectedQReadback
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary readbackESealRead
  have supportUnary : UnaryHistory support :=
    unary_cont_closed sealReadUnary hUnary sealReadHSupport
  have completionUnary : UnaryHistory completion :=
    unary_cont_closed supportUnary cUnary supportCCompletion
  exact
    ⟨rootFrontUnary, selectedUnary, readbackUnary, sealReadUnary, supportUnary,
      completionUnary, m0m1u, m0URootFront, uvt, tWSelected, selectedQReadback,
      readbackESealRead, sealReadHSupport, supportCCompletion, pPkg, completionPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
