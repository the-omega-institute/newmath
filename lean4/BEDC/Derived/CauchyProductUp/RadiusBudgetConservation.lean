import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_radius_budget_conservation [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name radiusLedger budgetSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont radiusA radiusB radiusLedger ->
        Cont radiusLedger ledger budgetSeal ->
          PkgSig bundle budgetSeal pkg ->
            UnaryHistory radiusA ∧ UnaryHistory radiusB ∧ UnaryHistory radiusLedger ∧
              UnaryHistory budgetSeal ∧ Cont radiusA radiusB radiusLedger ∧
                Cont radiusLedger ledger budgetSeal ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle budgetSeal pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist Cont UnaryHistory ProbeBundle Pkg
  intro packet radiusRoute budgetRoute budgetSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, radiusAUnary,
    radiusBUnary, _observationAUnary, _observationBUnary, _routesUnary, ledgerUnary,
    _windowTransport, _productRoute, _classifierRoute, namePkg⟩ := packet
  have radiusLedgerUnary : UnaryHistory radiusLedger :=
    unary_cont_closed radiusAUnary radiusBUnary radiusRoute
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed radiusLedgerUnary ledgerUnary budgetRoute
  exact
    ⟨radiusAUnary, radiusBUnary, radiusLedgerUnary, budgetSealUnary, radiusRoute,
      budgetRoute, namePkg, budgetSealPkg⟩

end BEDC.Derived.CauchyProductUp
