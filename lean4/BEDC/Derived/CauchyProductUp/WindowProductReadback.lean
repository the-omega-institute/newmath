import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductWindowProductReadback [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont product ledger readback ->
        PkgSig bundle readback pkg ->
          UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
            UnaryHistory windowB ∧ UnaryHistory product ∧ UnaryHistory classifier ∧
              UnaryHistory readback ∧ Cont observationA observationB product ∧
                Cont product ledger classifier ∧ Cont product ledger readback ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle readback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet productLedgerReadback readbackPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, _routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed productUnary ledgerUnary productLedgerReadback
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, productUnary,
      classifierUnary, readbackUnary, productRoute, classifierRoute, productLedgerReadback,
      namePkg, readbackPkg⟩

end BEDC.Derived.CauchyProductUp
