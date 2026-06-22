import BEDC.Derived.BaireCategoryUp.NameCertObligations
import BEDC.FKernel.Cont

namespace BEDC.Derived.BaireCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BaireCategoryCarrier_complete_metric_source_route [AskSetup] [PackageSetup]
    {B M D O R T H C P N streamRead regularRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  BaireCategoryCarrier B M D O R T H C P N bundle pkg ∧ Cont B M streamRead ∧
    Cont streamRead T regularRead ∧ Cont regularRead R realRead ∧ PkgSig bundle P pkg ∧
      PkgSig bundle realRead pkg

theorem BaireCategoryCarrier_complete_metric_source_route_closure [AskSetup] [PackageSetup]
    {B M D O R T H C P N streamRead regularRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireCategoryCarrier_complete_metric_source_route (B := B) (M := M) (D := D) (O := O)
        (R := R) (T := T) (H := H) (C := C) (P := P) (N := N)
        (streamRead := streamRead) (regularRead := regularRead) (realRead := realRead)
        (bundle := bundle) (pkg := pkg) →
      UnaryHistory streamRead ∧ UnaryHistory regularRead ∧ UnaryHistory realRead ∧
        PkgSig bundle P pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro route
  obtain ⟨carrier, streamRoute, regularRoute, realRoute, provenancePkg, realPkg⟩ := route
  obtain ⟨bUnary, mUnary, _dUnary, _oUnary, rUnary, tUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _carrierPkg⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed bUnary mUnary streamRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed streamUnary tUnary regularRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary rUnary realRoute
  exact ⟨streamUnary, regularUnary, realUnary, provenancePkg, realPkg⟩

end BEDC.Derived.BaireCategoryUp
