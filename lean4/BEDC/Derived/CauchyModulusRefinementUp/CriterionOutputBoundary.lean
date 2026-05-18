import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_criterion_output_boundary [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n criterion uniform boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont u v t ->
        Cont t w q ->
          Cont q e boundary ->
            Cont criterion uniform boundary ->
              PkgSig bundle boundary pkg ->
                UnaryHistory u ∧ UnaryHistory v ∧ UnaryHistory t ∧ UnaryHistory w ∧
                  UnaryHistory q ∧ UnaryHistory e ∧ UnaryHistory boundary ∧
                    Cont u v t ∧ Cont t w q ∧ Cont q e boundary ∧
                      Cont criterion uniform boundary ∧ PkgSig bundle p pkg ∧
                        PkgSig bundle boundary pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier uvtArg twqArg qeboundary criterionUniformBoundary boundaryPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, uUnary, vUnary, _tUnary, wUnary, _qUnary, eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, _carrierUvt, _carrierTwq,
      _qeh, pPkg, _hn⟩
  have tUnary : UnaryHistory t :=
    unary_cont_closed uUnary vUnary uvtArg
  have qUnary : UnaryHistory q :=
    unary_cont_closed tUnary wUnary twqArg
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed qUnary eUnary qeboundary
  exact
    ⟨uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, boundaryUnary, uvtArg,
      twqArg, qeboundary, criterionUniformBoundary, pPkg, boundaryPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
