import BEDC.Derived.LocatedSupremumUp.Carrier

namespace BEDC.Derived.LocatedSupremumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedSupremumCarrier_streamname_cut_scope [AskSetup] [PackageSetup]
    {L U A W R E H C P N cutRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedSupremumCarrier L U A W R E H C P N bundle pkg ->
      Cont W R cutRead ->
        Cont cutRead E realRead ->
          PkgSig bundle realRead pkg ->
            UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory cutRead ∧ UnaryHistory realRead ∧
              hsame L U ∧ Cont W R cutRead ∧ Cont cutRead E realRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: LocatedSupremumCarrier BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier cutRoute realRoute realPkg
  have unaryR : UnaryHistory R := carrier.left
  have unaryA : UnaryHistory A := carrier.right.left
  have carrierRoute : Cont R A E := carrier.right.right.left
  have hLU : hsame L U := carrier.right.right.right.left
  have unaryW : UnaryHistory W := carrier.right.right.right.right.left
  have pkgSig : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.left
  have unaryE : UnaryHistory E :=
    unary_cont_closed unaryR unaryA carrierRoute
  have cutUnary : UnaryHistory cutRead :=
    unary_cont_closed unaryW unaryR cutRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed cutUnary unaryE realRoute
  exact ⟨unaryW, unaryR, cutUnary, realUnary, hLU, cutRoute, realRoute, pkgSig, realPkg⟩

end BEDC.Derived.LocatedSupremumUp
