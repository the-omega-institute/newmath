import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementRootThresholdOpenPhaseHandoff [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n rootRead selected readback sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont m0 u rootRead →
        Cont t w selected →
          Cont selected q readback →
            Cont readback e sealRead →
              Cont sealRead h publicRead →
                PkgSig bundle publicRead pkg →
                  UnaryHistory rootRead ∧ UnaryHistory selected ∧ UnaryHistory readback ∧
                    UnaryHistory sealRead ∧ UnaryHistory publicRead ∧ Cont m0 u rootRead ∧
                      Cont u v t ∧ Cont t w selected ∧ Cont selected q readback ∧
                        Cont readback e sealRead ∧ Cont sealRead h publicRead ∧
                          PkgSig bundle p pkg ∧ PkgSig bundle publicRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame UnaryHistory
  intro carrier m0Root rootSelected selectedReadback readbackSeal sealPublic publicPkg
  rcases carrier with
    ⟨m0Unary, _m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      _cUnary, _pUnary, _nUnary, _m0m1u, uvt, _twq, _qeh, pPkg, hn⟩
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed m0Unary uUnary m0Root
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary rootSelected
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary selectedReadback
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary readbackSeal
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary hUnary sealPublic
  exact
    ⟨rootUnary, selectedUnary, readbackUnary, sealUnary, publicUnary, m0Root, uvt,
      rootSelected, selectedReadback, readbackSeal, sealPublic, pPkg, publicPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
