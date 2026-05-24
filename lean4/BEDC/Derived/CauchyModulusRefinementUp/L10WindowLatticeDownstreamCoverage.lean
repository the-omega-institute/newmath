import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_l10_window_lattice_downstream_coverage
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n sourceRead faceRead coverageRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont m0 u sourceRead ->
        Cont t w faceRead ->
          Cont h c coverageRead ->
            PkgSig bundle coverageRead pkg ->
              UnaryHistory sourceRead ∧ UnaryHistory faceRead ∧
                UnaryHistory coverageRead ∧ Cont m0 u sourceRead ∧
                  Cont t w faceRead ∧ Cont h c coverageRead ∧ PkgSig bundle p pkg ∧
                    PkgSig bundle coverageRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory hsame
  intro carrier sourceRoute faceRoute coverageRoute coveragePkg
  obtain ⟨m0Unary, _m1Unary, uUnary, _vUnary, tUnary, wUnary, _qUnary, _eUnary,
    hUnary, cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, pPkg, hn⟩ :=
    carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed m0Unary uUnary sourceRoute
  have faceUnary : UnaryHistory faceRead :=
    unary_cont_closed tUnary wUnary faceRoute
  have coverageUnary : UnaryHistory coverageRead :=
    unary_cont_closed hUnary cUnary coverageRoute
  exact
    ⟨sourceUnary, faceUnary, coverageUnary, sourceRoute, faceRoute, coverageRoute, pPkg,
      coveragePkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
