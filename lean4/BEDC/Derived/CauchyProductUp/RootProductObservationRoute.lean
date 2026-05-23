import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_root_product_observation_route [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name productRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont transport routes productRead ->
        PkgSig bundle productRead pkg ->
          UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
            UnaryHistory windowB ∧ UnaryHistory observationA ∧ UnaryHistory observationB ∧
              UnaryHistory product ∧ UnaryHistory productRead ∧ Cont windowA windowB transport ∧
                Cont observationA observationB product ∧ Cont transport routes productRead ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle productRead pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro packet productReadRoute productReadPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, _ledgerUnary,
    windowTransport, productRoute, _classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed windowAUnary windowBUnary windowTransport
  have productReadUnary : UnaryHistory productRead :=
    unary_cont_closed transportUnary routesUnary productReadRoute
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, observationAUnary,
      observationBUnary, productUnary, productReadUnary, windowTransport, productRoute,
      productReadRoute, namePkg, productReadPkg⟩

end BEDC.Derived.CauchyProductUp
