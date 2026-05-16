import BEDC.Derived.CauchyModulusRefinementUp
import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.UniformCauchyCriterionUp

theorem CauchyModulusRefinementCarrier_uniform_criterion_real_route_determinacy
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n ui uw um utail useal utrans uroutes upkg uname :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      UniformCauchyCriterionPacket ui uw um q utail useal utrans uroutes upkg uname
        bundle pkg ->
        hsame w uw ->
          hsame e useal ->
            UnaryHistory w ∧ UnaryHistory q ∧ UnaryHistory e ∧ UnaryHistory uw ∧
              UnaryHistory useal ∧ Cont t w q ∧ Cont um q utail ∧ hsame w uw ∧
                hsame e useal ∧ PkgSig bundle p pkg ∧ PkgSig bundle uname pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  intro refinement uniform sameWindow sameSeal
  obtain ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, wUnary, qUnary, eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, twq, _qeh, pPkg, _hn⟩ :=
    refinement
  obtain ⟨_uiUnary, uwUnary, _umUnary, _qUnaryUniform, _utailUnary, usealUnary,
    _utransUnary, _uroutesUnary, _upkgUnary, _unameUnary, _uiUwUm, umQUtail,
    _utailUsealUtrans, _utransUroutesUpkg, unamePkg⟩ := uniform
  exact
    ⟨wUnary, qUnary, eUnary, uwUnary, usealUnary, twq, umQUtail, sameWindow, sameSeal,
      pPkg, unamePkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
