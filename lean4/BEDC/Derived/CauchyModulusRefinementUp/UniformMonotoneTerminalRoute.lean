import BEDC.Derived.CauchyModulusRefinementUp
import BEDC.Derived.MonotoneCauchyUp
import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.MonotoneCauchyUp
open BEDC.Derived.UniformCauchyCriterionUp

theorem CauchyModulusRefinementCarrier_uniform_monotone_terminal_route
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n ui uw um utail useal utrans uroutes upkg uname mr ms
      mm ml mi mseal mtransport mroute mprovenance mname terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      UniformCauchyCriterionPacket ui uw um q utail useal utrans uroutes upkg uname
        bundle pkg ->
        MonotoneCauchyCarrier mr ms mm ml mi mseal mtransport mroute mprovenance mname
          bundle pkg ->
          hsame w uw ->
            hsame e useal ->
              hsame e mseal ->
                Cont q e terminal ->
                  PkgSig bundle terminal pkg ->
                    UnaryHistory terminal ∧ Cont m0 m1 u ∧ Cont u v t ∧ Cont t w q ∧
                      Cont q e terminal ∧ hsame w uw ∧ hsame e useal ∧ hsame e mseal ∧
                        PkgSig bundle p pkg ∧ PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  intro refinement uniform monotone sameUniformWindow sameUniformSeal sameMonotoneSeal
    terminalRoute terminalPkg
  obtain ⟨_uiUnary, _uwUnary, _umUnary, _qUnaryUniform, _utailUnary, _usealUnary,
    _utransUnary, _uroutesUnary, _upkgUnary, _unameUnary, _uiUwUm, _umQUtail,
    _utailUsealUtrans, _utransUroutesUpkg, _unamePkg⟩ := uniform
  obtain ⟨_mrUnary, _msUnary, _mmUnary, _mlUnary, _miUnary, _msealUnary,
    _mtransportUnary, _mrouteUnary, _monotoneProvenanceUnary, _monotoneNameUnary,
    _mrMsMm, _mmMlMi, _miMsealMonotoneName, _mtransportMrouteProvenance,
    _monotoneNamePkg⟩ := monotone
  obtain ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, _wUnary, qUnary, eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, m0m1u, uvt, twq, _qeh, pPkg, _hn⟩ :=
    refinement
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed qUnary eUnary terminalRoute
  exact
    ⟨terminalUnary, m0m1u, uvt, twq, terminalRoute, sameUniformWindow,
      sameUniformSeal, sameMonotoneSeal, pPkg, terminalPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
