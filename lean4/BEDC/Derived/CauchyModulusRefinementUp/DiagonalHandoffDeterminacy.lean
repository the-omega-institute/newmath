import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementDiagonalHandoffDeterminacy [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w selected ->
        Cont selected q readback ->
          Cont readback e sealRead ->
            Cont sealRead h publicRead ->
              PkgSig bundle publicRead pkg ->
                UnaryHistory selected ∧ UnaryHistory readback ∧ UnaryHistory sealRead ∧
                  UnaryHistory publicRead ∧ Cont t w selected ∧ Cont selected q readback ∧
                    Cont readback e sealRead ∧ Cont sealRead h publicRead ∧
                      PkgSig bundle p pkg ∧ PkgSig bundle publicRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame
  intro carrier tWSelected selectedQReadback readbackESeal sealHPublic publicPkg
  obtain ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, eUnary,
    hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, pPkg, hN⟩ := carrier
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary tWSelected
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary selectedQReadback
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary readbackESeal
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed sealReadUnary hUnary sealHPublic
  exact
    ⟨selectedUnary, readbackUnary, sealReadUnary, publicReadUnary, tWSelected,
      selectedQReadback, readbackESeal, sealHPublic, pPkg, publicPkg, hN⟩

end BEDC.Derived.CauchyModulusRefinementUp
