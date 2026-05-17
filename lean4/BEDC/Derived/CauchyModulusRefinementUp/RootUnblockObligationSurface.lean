import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp.RootUnblockObligationSurface

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.CauchyModulusRefinementUp

theorem CauchyModulusRefinementCarrier_current_phase_spine [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont t w selected →
        Cont selected q readback →
          Cont readback e sealRead →
            Cont sealRead h publicRead →
              PkgSig bundle publicRead pkg →
                UnaryHistory selected ∧ UnaryHistory readback ∧ UnaryHistory sealRead ∧
                  UnaryHistory publicRead ∧ Cont m0 m1 u ∧ Cont u v t ∧
                    Cont t w selected ∧ Cont selected q readback ∧
                      Cont readback e sealRead ∧ Cont sealRead h publicRead ∧
                        PkgSig bundle p pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier twSelected selectedQReadback readbackESealRead sealReadHPublicRead publicReadPkg
  obtain ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
    _cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, _qeh, pPkg, _hn⟩ :=
    carrier
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary twSelected
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary selectedQReadback
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary readbackESealRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed sealReadUnary hUnary sealReadHPublicRead
  exact
    ⟨selectedUnary, readbackUnary, sealReadUnary, publicReadUnary, m0m1u, uvt,
      twSelected, selectedQReadback, readbackESealRead, sealReadHPublicRead, pPkg,
      publicReadPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp.RootUnblockObligationSurface
