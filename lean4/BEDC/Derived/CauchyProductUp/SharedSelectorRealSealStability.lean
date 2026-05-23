import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_shared_selector_real_seal_stability [AskSetup] [PackageSetup]
    {sourceA1 sourceB1 windowA1 windowB1 radiusA1 radiusB1 observationA1 observationB1
      product1 classifier1 transport1 routes1 ledger1 name1 sourceA2 sourceB2 windowA2
      windowB2 radiusA2 radiusB2 observationA2 observationB2 product2 classifier2 transport2
      routes2 ledger2 name2 selectorWindow selectorDyadic selectorRegular seal1 seal2 : BHist}
    {bundle1 bundle2 selectorBundle : ProbeBundle ProbeName} {pkg1 pkg2 selectorPkg : Pkg} :
    CauchyProductPacket sourceA1 sourceB1 windowA1 windowB1 radiusA1 radiusB1 observationA1
        observationB1 product1 classifier1 transport1 routes1 ledger1 name1 bundle1 pkg1 ->
      CauchyProductPacket sourceA2 sourceB2 windowA2 windowB2 radiusA2 radiusB2 observationA2
          observationB2 product2 classifier2 transport2 routes2 ledger2 name2 bundle2 pkg2 ->
        hsame product1 product2 ->
          Cont selectorWindow selectorDyadic selectorRegular ->
            Cont product1 selectorRegular seal1 ->
              Cont product2 selectorRegular seal2 ->
                PkgSig selectorBundle selectorRegular selectorPkg ->
                  UnaryHistory selectorWindow ->
                    UnaryHistory selectorDyadic ->
                      UnaryHistory seal1 ∧ UnaryHistory seal2 ∧ hsame seal1 seal2 ∧
                        Cont product1 selectorRegular seal1 ∧
                          Cont product2 selectorRegular seal2 := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory PkgSig
  intro packet1 packet2 sameProduct selectorRoute sealRoute1 sealRoute2 _selectorPkg
    selectorWindowUnary selectorDyadicUnary
  obtain ⟨_sourceA1Unary, _sourceB1Unary, _windowA1Unary, _windowB1Unary, _radiusA1Unary,
    _radiusB1Unary, observationA1Unary, observationB1Unary, _routes1Unary, _ledger1Unary,
    _windowTransport1, productRoute1, _classifierRoute1, _namePkg1⟩ := packet1
  obtain ⟨_sourceA2Unary, _sourceB2Unary, _windowA2Unary, _windowB2Unary, _radiusA2Unary,
    _radiusB2Unary, observationA2Unary, observationB2Unary, _routes2Unary, _ledger2Unary,
    _windowTransport2, productRoute2, _classifierRoute2, _namePkg2⟩ := packet2
  have product1Unary : UnaryHistory product1 :=
    unary_cont_closed observationA1Unary observationB1Unary productRoute1
  have product2Unary : UnaryHistory product2 :=
    unary_cont_closed observationA2Unary observationB2Unary productRoute2
  have selectorRegularUnary : UnaryHistory selectorRegular :=
    unary_cont_closed selectorWindowUnary selectorDyadicUnary selectorRoute
  have seal1Unary : UnaryHistory seal1 :=
    unary_cont_closed product1Unary selectorRegularUnary sealRoute1
  have seal2Unary : UnaryHistory seal2 :=
    unary_cont_closed product2Unary selectorRegularUnary sealRoute2
  have sameSeals : hsame seal1 seal2 :=
    cont_respects_hsame sameProduct (hsame_refl selectorRegular) sealRoute1 sealRoute2
  exact ⟨seal1Unary, seal2Unary, sameSeals, sealRoute1, sealRoute2⟩

end BEDC.Derived.CauchyProductUp
