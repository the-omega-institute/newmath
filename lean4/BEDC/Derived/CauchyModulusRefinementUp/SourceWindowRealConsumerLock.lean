import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_source_window_real_consumer_lock
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n rootFront selected readback sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont m0 u rootFront →
        Cont t w selected →
          Cont selected q readback →
            Cont readback e sealRead →
              Cont sealRead h publicRead →
                PkgSig bundle publicRead pkg →
                  UnaryHistory rootFront ∧ UnaryHistory selected ∧ UnaryHistory readback ∧
                    UnaryHistory sealRead ∧ UnaryHistory publicRead ∧ Cont m0 m1 u ∧
                      Cont m0 u rootFront ∧ Cont u v t ∧ Cont t w selected ∧
                        Cont selected q readback ∧ Cont readback e sealRead ∧
                          Cont sealRead h publicRead ∧ PkgSig bundle p pkg ∧
                            PkgSig bundle publicRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier m0URoot tWSelected selectedQReadback readbackESeal sealHPublic publicPkg
  rcases carrier with
    ⟨m0Unary, _m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary, _cUnary,
      _pUnary, _nUnary, m0m1u, uvt, _twq, _qeh, pPkg, hn⟩
  have rootUnary : UnaryHistory rootFront :=
    unary_cont_closed m0Unary uUnary m0URoot
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary tWSelected
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary selectedQReadback
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary readbackESeal
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed sealReadUnary hUnary sealHPublic
  exact
    ⟨rootUnary, selectedUnary, readbackUnary, sealReadUnary, publicReadUnary, m0m1u,
      m0URoot, uvt, tWSelected, selectedQReadback, readbackESeal, sealHPublic, pPkg,
      publicPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
