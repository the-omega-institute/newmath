import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_window_product_nonescape [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name leftWindowRead rightWindowRead
      windowProduct : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont sourceA windowA leftWindowRead ->
        Cont sourceB windowB rightWindowRead ->
          Cont leftWindowRead rightWindowRead windowProduct ->
            PkgSig bundle windowProduct pkg ->
              UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
                UnaryHistory windowB ∧ UnaryHistory leftWindowRead ∧
                  UnaryHistory rightWindowRead ∧ UnaryHistory windowProduct ∧
                    Cont sourceA windowA leftWindowRead ∧
                      Cont sourceB windowB rightWindowRead ∧
                        Cont leftWindowRead rightWindowRead windowProduct ∧
                          Cont observationA observationB product ∧ PkgSig bundle name pkg ∧
                            PkgSig bundle windowProduct pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet leftReadRoute rightReadRoute windowProductRoute windowProductPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, _observationAUnary, _observationBUnary, _routesUnary, _ledgerUnary,
    _windowTransport, productRoute, _classifierRoute, namePkg⟩ := packet
  have leftWindowReadUnary : UnaryHistory leftWindowRead :=
    unary_cont_closed sourceAUnary windowAUnary leftReadRoute
  have rightWindowReadUnary : UnaryHistory rightWindowRead :=
    unary_cont_closed sourceBUnary windowBUnary rightReadRoute
  have windowProductUnary : UnaryHistory windowProduct :=
    unary_cont_closed leftWindowReadUnary rightWindowReadUnary windowProductRoute
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, leftWindowReadUnary,
      rightWindowReadUnary, windowProductUnary, leftReadRoute, rightReadRoute,
      windowProductRoute, productRoute, namePkg, windowProductPkg⟩

end BEDC.Derived.CauchyProductUp
