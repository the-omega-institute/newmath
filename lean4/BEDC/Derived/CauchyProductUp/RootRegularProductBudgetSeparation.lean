import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_root_regular_product_budget_separation [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name sealRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont product classifier sealRead ->
        Cont sealRead name exportRead ->
          PkgSig bundle ledger pkg ->
            PkgSig bundle name pkg ->
              UnaryHistory name ->
                UnaryHistory sealRead ∧ UnaryHistory exportRead ∧
                  Cont product classifier sealRead ∧ Cont sealRead name exportRead ∧
                    PkgSig bundle ledger pkg ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet productClassifierSeal sealNameExport ledgerPkg namePkg nameUnary
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, _routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, _packetNamePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed productUnary classifierUnary productClassifierSeal
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed sealReadUnary nameUnary sealNameExport
  exact
    ⟨sealReadUnary, exportReadUnary, productClassifierSeal, sealNameExport, ledgerPkg,
      namePkg⟩

end BEDC.Derived.CauchyProductUp
