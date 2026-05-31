import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_product_window_consumer_handoff [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name realSeal orderBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes realSeal ->
        Cont realSeal ledger orderBoundary ->
          PkgSig bundle orderBoundary pkg ->
            UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory product ∧
              UnaryHistory classifier ∧ UnaryHistory realSeal ∧ UnaryHistory orderBoundary ∧
                Cont observationA observationB product ∧ Cont product ledger classifier ∧
                  Cont classifier routes realSeal ∧ Cont realSeal ledger orderBoundary ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle orderBoundary pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierRoutesRealSeal realSealLedgerOrderBoundary orderBoundaryPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed classifierUnary routesUnary classifierRoutesRealSeal
  have orderBoundaryUnary : UnaryHistory orderBoundary :=
    unary_cont_closed realSealUnary ledgerUnary realSealLedgerOrderBoundary
  exact
    ⟨windowAUnary, windowBUnary, productUnary, classifierUnary, realSealUnary,
      orderBoundaryUnary, productRoute, classifierRoute, classifierRoutesRealSeal,
      realSealLedgerOrderBoundary, namePkg, orderBoundaryPkg⟩

end BEDC.Derived.CauchyProductUp
