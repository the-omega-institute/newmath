import BEDC.Derived.BaireCategoryUp.NameCertObligations
import BEDC.FKernel.Cont

namespace BEDC.Derived.BaireCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireCategoryCarrier_l10_completion_source_boundary [AskSetup] [PackageSetup]
    {B M D O R T H C P N streamRead regularRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireCategoryCarrier B M D O R T H C P N bundle pkg ->
      Cont B M streamRead ->
        Cont streamRead T regularRead ->
          Cont regularRead R realRead ->
            PkgSig bundle realRead pkg ->
              UnaryHistory B ∧ UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory T ∧
                UnaryHistory streamRead ∧ UnaryHistory regularRead ∧ UnaryHistory realRead ∧
                  Cont B M streamRead ∧ Cont streamRead T regularRead ∧
                    Cont regularRead R realRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier streamRoute regularRoute realRoute realPkg
  obtain ⟨bUnary, mUnary, _dUnary, _oUnary, rUnary, tUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, provenancePkg⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed bUnary mUnary streamRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed streamUnary tUnary regularRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary rUnary realRoute
  exact
    ⟨bUnary, mUnary, rUnary, tUnary, streamUnary, regularUnary, realUnary, streamRoute,
      regularRoute, realRoute, provenancePkg, realPkg⟩

end BEDC.Derived.BaireCategoryUp
