import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_realalgorder_multiplication_export [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name swappedProduct swappedClassifier
      multiplicationExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont observationB observationA swappedProduct ->
        Cont swappedProduct ledger swappedClassifier ->
          Cont classifier swappedClassifier multiplicationExport ->
            PkgSig bundle multiplicationExport pkg ->
              UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory swappedProduct ∧
                UnaryHistory swappedClassifier ∧ UnaryHistory multiplicationExport ∧
                  Cont observationA observationB product ∧ Cont product ledger classifier ∧
                    Cont observationB observationA swappedProduct ∧
                      Cont swappedProduct ledger swappedClassifier ∧
                        Cont classifier swappedClassifier multiplicationExport ∧
                          PkgSig bundle name pkg ∧
                            PkgSig bundle multiplicationExport pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet swappedProductRoute swappedClassifierRoute multiplicationExportRoute
    multiplicationExportPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, _routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have swappedProductUnary : UnaryHistory swappedProduct :=
    unary_cont_closed observationBUnary observationAUnary swappedProductRoute
  have swappedClassifierUnary : UnaryHistory swappedClassifier :=
    unary_cont_closed swappedProductUnary ledgerUnary swappedClassifierRoute
  have multiplicationExportUnary : UnaryHistory multiplicationExport :=
    unary_cont_closed classifierUnary swappedClassifierUnary multiplicationExportRoute
  exact
    ⟨productUnary, classifierUnary, swappedProductUnary, swappedClassifierUnary,
      multiplicationExportUnary, productRoute, classifierRoute, swappedProductRoute,
      swappedClassifierRoute, multiplicationExportRoute, namePkg, multiplicationExportPkg⟩

end BEDC.Derived.CauchyProductUp
