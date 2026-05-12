import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicTailBoundUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicTailBoundCarrier [AskSetup] [PackageSetup]
    (precision schedule tolerance ledger readback «seal» transport route provenance
      localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory schedule ∧ UnaryHistory tolerance ∧
    UnaryHistory readback ∧ UnaryHistory «seal» ∧ UnaryHistory provenance ∧
      Cont schedule tolerance ledger ∧ Cont ledger readback «seal» ∧
        Cont precision «seal» transport ∧ Cont transport localCert route ∧
          Cont route provenance «seal» ∧ PkgSig bundle provenance pkg

theorem DyadicTailBoundCarrier_regseqrat_handoff_exactness [AskSetup] [PackageSetup]
    {precision schedule tolerance ledger readback «seal» transport route provenance localCert
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicTailBoundCarrier precision schedule tolerance ledger readback «seal» transport route
        provenance localCert bundle pkg ->
      Cont ledger readback consumerRead ->
        UnaryHistory precision ∧ UnaryHistory schedule ∧ UnaryHistory tolerance ∧
          UnaryHistory ledger ∧ UnaryHistory readback ∧ UnaryHistory consumerRead ∧
            Cont schedule tolerance ledger ∧ Cont ledger readback consumerRead ∧
              PkgSig bundle provenance pkg := by
  intro carrier consumerRow
  obtain ⟨precisionUnary, scheduleUnary, toleranceUnary, readbackUnary, _sealUnary,
    _provenanceUnary, scheduleToleranceRow, _sealRow, _transportRow, _routeRow,
    _sealRouteRow, pkgSig⟩ := carrier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed scheduleUnary toleranceUnary scheduleToleranceRow
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed ledgerUnary readbackUnary consumerRow
  exact ⟨precisionUnary, scheduleUnary, toleranceUnary, ledgerUnary, readbackUnary,
    consumerUnary, scheduleToleranceRow, consumerRow, pkgSig⟩

end BEDC.Derived.DyadicTailBoundUp
