import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_real_seal_source_conservation
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n hSeal routed : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont q e hSeal ->
        Cont hSeal c routed ->
          PkgSig bundle routed pkg ->
            hsame h hSeal ∧ UnaryHistory routed ∧ Cont m0 m1 u ∧ Cont u v t ∧
              Cont q e hSeal ∧ Cont hSeal c routed ∧ PkgSig bundle routed pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  intro carrier hSealRow routedRow routedPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, _wUnary, qUnary, eUnary, hUnary,
      cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, carrierSealRow, _pPkg, _hn⟩
  have sameSeal : hsame h hSeal :=
    cont_respects_hsame (hsame_refl q) (hsame_refl e) carrierSealRow hSealRow
  have hSealUnary : UnaryHistory hSeal :=
    unary_cont_closed qUnary eUnary hSealRow
  have routedUnary : UnaryHistory routed :=
    unary_cont_closed hSealUnary cUnary routedRow
  exact ⟨sameSeal, routedUnary, m0m1u, uvt, hSealRow, routedRow, routedPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
