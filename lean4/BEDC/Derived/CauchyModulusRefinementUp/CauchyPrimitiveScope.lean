import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_primitive_scope [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      UnaryHistory m0 ∧ UnaryHistory m1 ∧ UnaryHistory u ∧ UnaryHistory v ∧
        UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory q ∧ UnaryHistory e ∧
          hsame h n ∧ PkgSig bundle p pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame UnaryHistory
  intro carrier
  obtain ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, pPkg,
    sameName⟩ := carrier
  exact
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary,
      sameName, pPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
