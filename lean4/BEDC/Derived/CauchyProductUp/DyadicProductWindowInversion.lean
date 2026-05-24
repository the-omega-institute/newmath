import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_dyadic_product_window_inversion [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name selectorWindow selectorDyadic selectorRegular
      productSeal : BHist}
    {bundle selectorBundle : ProbeBundle ProbeName} {pkg selectorPkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont selectorWindow selectorDyadic selectorRegular ->
        Cont product selectorRegular productSeal ->
          PkgSig selectorBundle selectorRegular selectorPkg ->
            UnaryHistory selectorWindow ->
              UnaryHistory selectorDyadic ->
                UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory observationA ∧
                  UnaryHistory observationB ∧ UnaryHistory product ∧
                    UnaryHistory selectorRegular ∧ UnaryHistory productSeal ∧
                      Cont observationA observationB product ∧
                        Cont selectorWindow selectorDyadic selectorRegular ∧
                          Cont product selectorRegular productSeal ∧ PkgSig bundle name pkg ∧
                            PkgSig selectorBundle selectorRegular selectorPkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist Cont UnaryHistory ProbeBundle Pkg
  intro packet selectorRegularRoute productSealRoute selectorRegularPkg selectorWindowUnary
    selectorDyadicUnary
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, _routesUnary, _ledgerUnary,
    _windowTransport, productRoute, _classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have selectorRegularUnary : UnaryHistory selectorRegular :=
    unary_cont_closed selectorWindowUnary selectorDyadicUnary selectorRegularRoute
  have productSealUnary : UnaryHistory productSeal :=
    unary_cont_closed productUnary selectorRegularUnary productSealRoute
  exact
    ⟨windowAUnary, windowBUnary, observationAUnary, observationBUnary, productUnary,
      selectorRegularUnary, productSealUnary, productRoute, selectorRegularRoute,
      productSealRoute, namePkg, selectorRegularPkg⟩

end BEDC.Derived.CauchyProductUp
