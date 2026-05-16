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
    {m0 m1 u v t w q e h c p n sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont q e sealRead ->
        PkgSig bundle sealRead pkg ->
          UnaryHistory m0 ∧ UnaryHistory m1 ∧ UnaryHistory u ∧ UnaryHistory v ∧
            UnaryHistory q ∧ UnaryHistory e ∧ UnaryHistory sealRead ∧ Cont m0 m1 u ∧
              Cont u v t ∧ Cont q e sealRead ∧ PkgSig bundle p pkg ∧
                PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier qSealRead sealReadPkg
  obtain ⟨m0Unary, m1Unary, uUnary, vUnary, _tUnary, _wUnary, qUnary, eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, _qeh, pPkg, _hn⟩ :=
    carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed qUnary eUnary qSealRead
  exact
    ⟨m0Unary, m1Unary, uUnary, vUnary, qUnary, eUnary, sealReadUnary, m0m1u, uvt,
      qSealRead, pPkg, sealReadPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
