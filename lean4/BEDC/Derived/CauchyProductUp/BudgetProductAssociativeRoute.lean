import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_budget_product_associative_route [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name leftProduct rightProduct sharedClassifier
      sharedSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg →
      Cont product routes leftProduct →
        Cont leftProduct ledger sharedClassifier →
          Cont observationA observationB rightProduct →
            Cont rightProduct ledger sharedClassifier →
              Cont sharedClassifier routes sharedSeal →
                PkgSig bundle sharedSeal pkg →
                  UnaryHistory leftProduct ∧ UnaryHistory rightProduct ∧
                    UnaryHistory sharedClassifier ∧ UnaryHistory sharedSeal ∧
                      Cont product routes leftProduct ∧
                        Cont leftProduct ledger sharedClassifier ∧
                          Cont rightProduct ledger sharedClassifier ∧
                            Cont sharedClassifier routes sharedSeal ∧
                              PkgSig bundle name pkg ∧ PkgSig bundle sharedSeal pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet productLeft leftClassifier observationRight rightClassifier classifierSeal
    sharedSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, _classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have leftProductUnary : UnaryHistory leftProduct :=
    unary_cont_closed productUnary routesUnary productLeft
  have rightProductUnary : UnaryHistory rightProduct :=
    unary_cont_closed observationAUnary observationBUnary observationRight
  have sharedClassifierUnary : UnaryHistory sharedClassifier :=
    unary_cont_closed leftProductUnary ledgerUnary leftClassifier
  have sharedSealUnary : UnaryHistory sharedSeal :=
    unary_cont_closed sharedClassifierUnary routesUnary classifierSeal
  exact
    ⟨leftProductUnary, rightProductUnary, sharedClassifierUnary, sharedSealUnary,
      productLeft, leftClassifier, rightClassifier, classifierSeal, namePkg, sharedSealPkg⟩

end BEDC.Derived.CauchyProductUp
