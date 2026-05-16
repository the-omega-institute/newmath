import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_open_phase_four_object_consumption [AskSetup]
    [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w selected ->
        Cont selected q readback ->
          Cont readback e sealRead ->
            Cont sealRead h publicRead ->
              PkgSig bundle publicRead pkg ->
                UnaryHistory w ∧ UnaryHistory q ∧ UnaryHistory e ∧
                  UnaryHistory selected ∧ UnaryHistory readback ∧
                    UnaryHistory sealRead ∧ UnaryHistory publicRead ∧
                      Cont m0 m1 u ∧ Cont u v t ∧ Cont t w selected ∧
                        Cont selected q readback ∧ Cont readback e sealRead ∧
                          Cont sealRead h publicRead ∧ PkgSig bundle p pkg ∧
                            PkgSig bundle publicRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier tWindowSelected selectedQReadback readbackSeal sealPublic publicPkg
  obtain ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, eUnary,
    hUnary, _cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, _qeh, pPkg, hn⟩ :=
    carrier
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary tWindowSelected
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary selectedQReadback
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary readbackSeal
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary hUnary sealPublic
  exact
    ⟨wUnary, qUnary, eUnary, selectedUnary, readbackUnary, sealUnary, publicUnary,
      m0m1u, uvt, tWindowSelected, selectedQReadback, readbackSeal, sealPublic, pPkg,
      publicPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
