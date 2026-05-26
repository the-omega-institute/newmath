import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_realalgorder_product_observation_export [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal realSeal
      algebraExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
        Cont budgetClassifier ledger budgetSeal ->
          Cont budgetSeal transport realSeal ->
            Cont product realSeal algebraExport ->
              PkgSig bundle algebraExport pkg ->
                UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory budgetSeal ∧
                  UnaryHistory realSeal ∧ UnaryHistory algebraExport ∧
                    Cont observationA observationB product ∧ Cont product ledger classifier ∧
                      Cont budgetSeal transport realSeal ∧
                        Cont product realSeal algebraExport ∧ PkgSig bundle name pkg ∧
                          PkgSig bundle algebraExport pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierBudget budgetSealRoute realSealRoute algebraExportRoute
    algebraExportPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have budgetClassifierUnary : UnaryHistory budgetClassifier :=
    unary_cont_closed classifierUnary routesUnary classifierBudget
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetClassifierUnary ledgerUnary budgetSealRoute
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed windowAUnary windowBUnary windowTransport
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed budgetSealUnary transportUnary realSealRoute
  have algebraExportUnary : UnaryHistory algebraExport :=
    unary_cont_closed productUnary realSealUnary algebraExportRoute
  exact
    ⟨productUnary, classifierUnary, budgetSealUnary, realSealUnary, algebraExportUnary,
      productRoute, classifierRoute, realSealRoute, algebraExportRoute, namePkg,
      algebraExportPkg⟩

end BEDC.Derived.CauchyProductUp
