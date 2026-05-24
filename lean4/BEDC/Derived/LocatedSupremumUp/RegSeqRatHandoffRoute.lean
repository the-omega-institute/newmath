import BEDC.Derived.LocatedSupremumUp.Carrier

namespace BEDC.Derived.LocatedSupremumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedSupremumCarrier_regseqrat_handoff_route [AskSetup] [PackageSetup]
    {L U A W R E H C P N bracketRead handoffRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedSupremumCarrier L U A W R E H C P N bundle pkg ->
      Cont W A bracketRead ->
        Cont bracketRead R handoffRead ->
          Cont handoffRead E consumer ->
            UnaryHistory bracketRead ∧ UnaryHistory handoffRead ∧ UnaryHistory consumer ∧
              Cont W A bracketRead ∧ Cont bracketRead R handoffRead ∧
                Cont handoffRead E consumer ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: LocatedSupremumCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier bracketRoute handoffRoute consumerRoute
  have unaryR : UnaryHistory R := carrier.left
  have unaryA : UnaryHistory A := carrier.right.left
  have carrierRoute : Cont R A E := carrier.right.right.left
  have unaryW : UnaryHistory W := carrier.right.right.right.right.left
  have pkgSig : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.left
  have unaryE : UnaryHistory E :=
    unary_cont_closed unaryR unaryA carrierRoute
  have bracketUnary : UnaryHistory bracketRead :=
    unary_cont_closed unaryW unaryA bracketRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed bracketUnary unaryR handoffRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed handoffUnary unaryE consumerRoute
  exact
    ⟨bracketUnary, handoffUnary, consumerUnary, bracketRoute, handoffRoute, consumerRoute,
      pkgSig⟩

theorem LocatedSupremumCarrier_regseqrat_real_handoff_stability [AskSetup] [PackageSetup]
    {L U A W R E H C P N approximationRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedSupremumCarrier L U A W R E H C P N bundle pkg ->
      Cont A R approximationRead ->
        Cont approximationRead E realRead ->
          PkgSig bundle realRead pkg ->
            UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory approximationRead ∧
              UnaryHistory realRead ∧ Cont A R approximationRead ∧
                Cont approximationRead E realRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: LocatedSupremumCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier approximationRoute realRoute realPkg
  have unaryR : UnaryHistory R := carrier.left
  have unaryA : UnaryHistory A := carrier.right.left
  have carrierRoute : Cont R A E := carrier.right.right.left
  have pkgSig : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.left
  have unaryE : UnaryHistory E :=
    unary_cont_closed unaryR unaryA carrierRoute
  have approximationUnary : UnaryHistory approximationRead :=
    unary_cont_closed unaryA unaryR approximationRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed approximationUnary unaryE realRoute
  exact
    ⟨unaryR, unaryE, approximationUnary, realUnary, approximationRoute, realRoute, pkgSig,
      realPkg⟩

end BEDC.Derived.LocatedSupremumUp
