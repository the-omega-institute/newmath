import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_budget_product_symmetric_route [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name swappedTransport swappedProduct budgetClassifier
      budgetSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg →
      Cont windowB windowA swappedTransport →
        Cont observationB observationA swappedProduct →
          Cont classifier routes budgetClassifier →
            Cont budgetClassifier ledger budgetSeal →
              PkgSig bundle budgetSeal pkg →
                UnaryHistory windowB ∧ UnaryHistory windowA ∧
                  UnaryHistory swappedTransport ∧ UnaryHistory swappedProduct ∧
                    UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                      Cont windowB windowA swappedTransport ∧
                        Cont observationB observationA swappedProduct ∧
                          Cont classifier routes budgetClassifier ∧
                            Cont budgetClassifier ledger budgetSeal ∧
                              PkgSig bundle name pkg ∧ PkgSig bundle budgetSeal pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet swappedWindowRoute swappedProductRoute classifierBudget budgetSealRoute
    budgetSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have swappedTransportUnary : UnaryHistory swappedTransport :=
    unary_cont_closed windowBUnary windowAUnary swappedWindowRoute
  have swappedProductUnary : UnaryHistory swappedProduct :=
    unary_cont_closed observationBUnary observationAUnary swappedProductRoute
  have budgetClassifierUnary : UnaryHistory budgetClassifier :=
    unary_cont_closed classifierUnary routesUnary classifierBudget
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetClassifierUnary ledgerUnary budgetSealRoute
  exact
    ⟨windowBUnary, windowAUnary, swappedTransportUnary, swappedProductUnary,
      budgetClassifierUnary, budgetSealUnary, swappedWindowRoute, swappedProductRoute,
      classifierBudget, budgetSealRoute, namePkg, budgetSealPkg⟩

end BEDC.Derived.CauchyProductUp
