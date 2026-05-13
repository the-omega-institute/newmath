import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ContinuationTraceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

structure ContinuationTracePacket [AskSetup] [PackageSetup] where
  source : BHist
  markTail : BHist
  target : BHist
  traceLedger : BHist
  transport : BHist
  continuation : BHist
  provenance : Pkg
  name : NameCert (fun row : BHist => hsame row target) hsame
  route_witness : Cont source markTail target
  source_transport : hsame source source
  target_transport : hsame target target

def ContinuationTraceCarrier [AskSetup] [PackageSetup]
    (source mark target ledger transports route provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory mark ∧ UnaryHistory target ∧ UnaryHistory ledger ∧
    UnaryHistory transports ∧ UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory cert ∧
      Cont source mark target ∧ Cont target ledger route ∧ Cont route cert provenance ∧
        PkgSig bundle provenance pkg

theorem ContinuationTraceCarrier_small_step_readback [AskSetup] [PackageSetup]
    {source mark target ledger transports route provenance cert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationTraceCarrier source mark target ledger transports route provenance cert bundle
        pkg →
      Cont route cert consumer →
        UnaryHistory source ∧ UnaryHistory mark ∧ UnaryHistory target ∧ UnaryHistory consumer ∧
          Cont source mark target ∧ Cont target ledger route ∧ PkgSig bundle provenance pkg := by
  intro carrier consumerRow
  obtain ⟨sourceUnary, markUnary, targetUnary, _ledgerUnary, _transportsUnary, routeUnary,
    _provenanceUnary, certUnary, sourceMarkTargetRow, targetLedgerRouteRow, _routeCertProvenanceRow,
    pkgSig⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary certUnary consumerRow
  exact ⟨sourceUnary, markUnary, targetUnary, consumerUnary, sourceMarkTargetRow,
    targetLedgerRouteRow, pkgSig⟩

theorem ContinuationTraceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source mark target ledger transports route provenance cert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationTraceCarrier source mark target ledger transports route provenance cert bundle pkg ->
      Cont route cert endpoint ->
        PkgSig bundle endpoint pkg ->
          SemanticNameCert
              (fun row : BHist =>
                ContinuationTraceCarrier source mark target ledger transports route provenance cert
                  bundle pkg ∧ hsame row endpoint)
              (fun row : BHist => hsame row provenance)
              (fun row : BHist => hsame row provenance ∧ PkgSig bundle endpoint pkg)
              hsame ∧
            UnaryHistory source ∧ UnaryHistory mark ∧ UnaryHistory target ∧
              UnaryHistory endpoint ∧ Cont source mark target ∧ Cont target ledger route ∧
                Cont route cert endpoint := by
  -- BEDC touchpoint anchor: BHist ContinuationTraceCarrier hsame SemanticNameCert
  intro carrier endpointRow endpointPkg
  have carrierWitness := carrier
  obtain ⟨sourceUnary, markUnary, targetUnary, _ledgerUnary, _transportsUnary, routeUnary,
    _provenanceUnary, certUnary, sourceMarkTargetRow, targetLedgerRouteRow,
    routeCertProvenanceRow, _pkgSig⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed routeUnary certUnary endpointRow
  have endpointSameProvenance : hsame endpoint provenance :=
    cont_deterministic endpointRow routeCertProvenanceRow
  have certCore :
      NameCert
        (fun row : BHist =>
          ContinuationTraceCarrier source mark target ledger transports route provenance cert
            bundle pkg ∧ hsame row endpoint)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro endpoint
        (And.intro carrierWitness (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
  have semantic :
      SemanticNameCert
          (fun row : BHist =>
            ContinuationTraceCarrier source mark target ledger transports route provenance cert
              bundle pkg ∧ hsame row endpoint)
          (fun row : BHist => hsame row provenance)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle endpoint pkg)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro _row sourceRow
        exact hsame_trans sourceRow.right endpointSameProvenance
      ledger_sound := by
        intro _row sourceRow
        exact And.intro (hsame_trans sourceRow.right endpointSameProvenance) endpointPkg
    }
  exact
    ⟨semantic, sourceUnary, markUnary, targetUnary, endpointUnary, sourceMarkTargetRow,
      targetLedgerRouteRow, endpointRow⟩

theorem ContinuationTraceCarrier_concatenation_readback [AskSetup] [PackageSetup]
    {source0 mark0 target0 ledger0 transports0 route0 provenance0 cert0 source1 mark1 target1
      ledger1 transports1 route1 provenance1 cert1 consumer : BHist}
    {bundle0 bundle1 : ProbeBundle ProbeName} {pkg0 pkg1 : Pkg} :
    ContinuationTraceCarrier source0 mark0 target0 ledger0 transports0 route0 provenance0 cert0
        bundle0 pkg0 ->
      ContinuationTraceCarrier source1 mark1 target1 ledger1 transports1 route1 provenance1 cert1
          bundle1 pkg1 ->
        hsame target0 source1 ->
          (Cont route0 cert0 consumer ∨ Cont route1 cert1 consumer) ->
            UnaryHistory consumer ∧ hsame target0 source1 ∧
              (Cont route0 cert0 consumer ∨ Cont route1 cert1 consumer) ∧
                (PkgSig bundle0 provenance0 pkg0 ∨ PkgSig bundle1 provenance1 pkg1) := by
  intro carrier0 carrier1 boundary routeChoice
  obtain ⟨_sourceUnary0, _markUnary0, _targetUnary0, _ledgerUnary0, _transportsUnary0,
    routeUnary0, _provenanceUnary0, certUnary0, _sourceMarkTargetRow0,
    _targetLedgerRouteRow0, _routeCertProvenanceRow0, pkgSig0⟩ := carrier0
  obtain ⟨_sourceUnary1, _markUnary1, _targetUnary1, _ledgerUnary1, _transportsUnary1,
    routeUnary1, _provenanceUnary1, certUnary1, _sourceMarkTargetRow1,
    _targetLedgerRouteRow1, _routeCertProvenanceRow1, pkgSig1⟩ := carrier1
  cases routeChoice with
  | inl route0Consumer =>
      have consumerUnary : UnaryHistory consumer :=
        unary_cont_closed routeUnary0 certUnary0 route0Consumer
      exact ⟨consumerUnary, boundary, Or.inl route0Consumer, Or.inl pkgSig0⟩
  | inr route1Consumer =>
      have consumerUnary : UnaryHistory consumer :=
        unary_cont_closed routeUnary1 certUnary1 route1Consumer
      exact ⟨consumerUnary, boundary, Or.inr route1Consumer, Or.inr pkgSig1⟩

theorem ContinuationTraceCarrier_endpoint_ledger_exhaustion [AskSetup] [PackageSetup]
    {source mark target ledger transports route provenance cert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationTraceCarrier source mark target ledger transports route provenance cert bundle
        pkg →
      (hsame endpoint source ∨ hsame endpoint target) →
        UnaryHistory endpoint ∧ UnaryHistory ledger ∧ UnaryHistory transports ∧
          Cont source mark target ∧ Cont target ledger route ∧ PkgSig bundle provenance pkg := by
  intro carrier endpointSame
  obtain ⟨sourceUnary, _markUnary, targetUnary, ledgerUnary, transportsUnary, _routeUnary,
    _provenanceUnary, _certUnary, sourceMarkTargetRow, targetLedgerRouteRow,
    _routeCertProvenanceRow, pkgSig⟩ := carrier
  have endpointUnary : UnaryHistory endpoint := by
    cases endpointSame with
    | inl sameSource =>
        exact unary_transport sourceUnary (hsame_symm sameSource)
    | inr sameTarget =>
        exact unary_transport targetUnary (hsame_symm sameTarget)
  exact ⟨endpointUnary, ledgerUnary, transportsUnary, sourceMarkTargetRow, targetLedgerRouteRow,
    pkgSig⟩

end BEDC.Derived.ContinuationTraceUp
