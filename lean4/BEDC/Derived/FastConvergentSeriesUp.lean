import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FastConvergentSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FastConvergentSeriesCarrier [AskSetup] [PackageSetup]
    (series seq partialSums schedule tailLedger regReadback realSeal transports routes
      provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory series ∧ UnaryHistory seq ∧ UnaryHistory partialSums ∧
    UnaryHistory schedule ∧ UnaryHistory tailLedger ∧ UnaryHistory regReadback ∧
      UnaryHistory realSeal ∧ UnaryHistory transports ∧ UnaryHistory routes ∧
        UnaryHistory nameCert ∧ Cont series seq partialSums ∧
          Cont schedule partialSums tailLedger ∧ Cont tailLedger regReadback realSeal ∧
            Cont realSeal provenance nameCert ∧ hsame tailLedger (append schedule partialSums) ∧
              hsame realSeal (append tailLedger regReadback) ∧
                PkgSig bundle provenance pkg

theorem FastConvergentSeriesCarrier_constant_zero_seed [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PkgSig bundle BHist.Empty pkg ->
      FastConvergentSeriesCarrier BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        bundle pkg := by
  intro pkgSig
  exact ⟨unary_empty, unary_empty, unary_empty, unary_empty, unary_empty, unary_empty,
    unary_empty, unary_empty, unary_empty, unary_empty, cont_left_unit BHist.Empty,
    cont_left_unit BHist.Empty, cont_left_unit BHist.Empty, cont_left_unit BHist.Empty,
    hsame_refl BHist.Empty, hsame_refl BHist.Empty, pkgSig⟩

theorem FastConvergentSeriesCarrier_tail_sum_boundary [AskSetup] [PackageSetup]
    {series seq partialSums schedule tailLedger regReadback realSeal transports routes provenance
      nameCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastConvergentSeriesCarrier series seq partialSums schedule tailLedger regReadback
        realSeal transports routes provenance nameCert bundle pkg ->
      Cont schedule partialSums tailLedger ->
        Cont tailLedger regReadback realSeal ->
          Cont realSeal provenance endpoint ->
            UnaryHistory tailLedger ∧ UnaryHistory realSeal ∧
              hsame tailLedger (append schedule partialSums) ∧
                hsame realSeal (append tailLedger regReadback) ∧
                  PkgSig bundle provenance pkg := by
  intro carrier scheduleBoundary realSealBoundary _endpointBoundary
  obtain ⟨_seriesUnary, _seqUnary, _partialUnary, _scheduleUnary, tailUnary,
    _realReadbackUnary, realSealUnary, _transportsUnary, _routesUnary, _nameCertUnary,
    _sourceRows, _carrierTailBoundary, _carrierSealBoundary, _nameCertBoundary,
    _tailSame, _sealSame, provenancePkg⟩ := carrier
  have tailBoundary : hsame tailLedger (append schedule partialSums) := by
    exact scheduleBoundary
  have sealBoundary : hsame realSeal (append tailLedger regReadback) := by
    exact realSealBoundary
  exact ⟨tailUnary, realSealUnary, tailBoundary, sealBoundary, provenancePkg⟩

theorem FastConvergentSeriesCarrier_bridge_tail_budget_schedule [AskSetup] [PackageSetup]
    {series seq partialSums schedule tailLedger regReadback realSeal transports routes provenance
      nameCert bridgeSchedule : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastConvergentSeriesCarrier series seq partialSums schedule tailLedger regReadback
        realSeal transports routes provenance nameCert bundle pkg ->
      Cont schedule partialSums tailLedger ->
        Cont tailLedger regReadback bridgeSchedule ->
          UnaryHistory schedule ∧ UnaryHistory partialSums ∧ UnaryHistory tailLedger ∧
            UnaryHistory bridgeSchedule ∧ Cont schedule partialSums tailLedger ∧
              Cont tailLedger regReadback bridgeSchedule ∧
                hsame tailLedger (append schedule partialSums) ∧
                  PkgSig bundle provenance pkg := by
  intro carrier scheduleBoundary bridgeBoundary
  obtain ⟨_seriesUnary, _seqUnary, partialSumsUnary, scheduleUnary, tailLedgerUnary,
    regReadbackUnary, _realSealUnary, _transportsUnary, _routesUnary, _nameCertUnary,
    _seriesRows, _carrierScheduleBoundary, _carrierSealBoundary, _nameCertBoundary,
    tailSame, _sealSame, provenancePkg⟩ := carrier
  have bridgeUnary : UnaryHistory bridgeSchedule :=
    unary_cont_closed tailLedgerUnary regReadbackUnary bridgeBoundary
  exact ⟨scheduleUnary, partialSumsUnary, tailLedgerUnary, bridgeUnary, scheduleBoundary,
    bridgeBoundary, tailSame, provenancePkg⟩

theorem FastConvergentSeriesCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {series seq partialSums schedule tailLedger regReadback realSeal transports routes provenance
      nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastConvergentSeriesCarrier series seq partialSums schedule tailLedger regReadback
        realSeal transports routes provenance nameCert bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row realSeal ∧
              FastConvergentSeriesCarrier series seq partialSums schedule tailLedger regReadback
                realSeal transports routes provenance nameCert bundle pkg)
          (fun row : BHist => hsame row realSeal)
          (fun row : BHist => hsame row realSeal ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory tailLedger ∧ UnaryHistory realSeal ∧ PkgSig bundle provenance pkg := by
  intro carrier
  have tailUnary : UnaryHistory tailLedger :=
    carrier.right.right.right.right.left
  have realSealUnary : UnaryHistory realSeal :=
    carrier.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right
  have sourceSeal :
      (fun row : BHist =>
        hsame row realSeal ∧
          FastConvergentSeriesCarrier series seq partialSums schedule tailLedger regReadback
            realSeal transports routes provenance nameCert bundle pkg) realSeal := by
    exact ⟨hsame_refl realSeal, carrier⟩
  have core :
      NameCert
        (fun row : BHist =>
          hsame row realSeal ∧
            FastConvergentSeriesCarrier series seq partialSums schedule tailLedger regReadback
              realSeal transports routes provenance nameCert bundle pkg)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro realSeal sourceSeal
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other same
        exact hsame_symm same
      equiv_trans := by
        intro row other third sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro row other same source
        constructor
        · exact hsame_trans (hsame_symm same) source.left
        · exact source.right
    }
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row realSeal ∧
              FastConvergentSeriesCarrier series seq partialSums schedule tailLedger regReadback
                realSeal transports routes provenance nameCert bundle pkg)
          (fun row : BHist => hsame row realSeal)
          (fun row : BHist => hsame row realSeal ∧ PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro row source
        exact source.left
      ledger_sound := by
        intro row source
        exact ⟨source.left, pkgSig⟩
    }
  exact ⟨cert, tailUnary, realSealUnary, pkgSig⟩

def FastConvergentSeriesTailBoundPacket [AskSetup] [PackageSetup]
    (summand partialSums schedule tailLedger regseqratReadback «seal» transport provenance
      localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory summand ∧ UnaryHistory partialSums ∧ UnaryHistory schedule ∧
    UnaryHistory regseqratReadback ∧ UnaryHistory «seal» ∧ UnaryHistory provenance ∧
      Cont partialSums schedule tailLedger ∧ Cont tailLedger regseqratReadback «seal» ∧
        Cont summand tailLedger transport ∧ Cont transport localCert provenance ∧
          PkgSig bundle provenance pkg

theorem FastConvergentSeriesTailBoundPacket_constant_zero_seed [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PkgSig bundle BHist.Empty pkg ->
      FastConvergentSeriesTailBoundPacket BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty bundle pkg := by
  intro pkgSig
  exact ⟨unary_empty, unary_empty, unary_empty, unary_empty, unary_empty, unary_empty,
    cont_left_unit BHist.Empty, cont_left_unit BHist.Empty, cont_left_unit BHist.Empty,
    cont_left_unit BHist.Empty, pkgSig⟩

theorem FastConvergentSeriesTailBoundPacket_regseqrat_handoff [AskSetup] [PackageSetup]
    {summand partialSums schedule tailLedger regseqratReadback «seal» transport provenance
      localCert consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastConvergentSeriesTailBoundPacket summand partialSums schedule tailLedger
        regseqratReadback «seal» transport provenance localCert bundle pkg ->
      Cont tailLedger regseqratReadback consumerRead ->
        UnaryHistory partialSums ∧ UnaryHistory schedule ∧ UnaryHistory tailLedger ∧
          UnaryHistory regseqratReadback ∧ UnaryHistory consumerRead ∧
            Cont partialSums schedule tailLedger ∧
              Cont tailLedger regseqratReadback consumerRead ∧
                PkgSig bundle provenance pkg := by
  intro packet consumerRow
  obtain ⟨_summandUnary, partialSumsUnary, scheduleUnary, regseqratReadbackUnary,
    _sealUnary, _provenanceUnary, partialScheduleRow, _sealRow, _transportRow,
    _provenanceRow, pkgSig⟩ := packet
  have tailLedgerUnary : UnaryHistory tailLedger :=
    unary_cont_closed partialSumsUnary scheduleUnary partialScheduleRow
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed tailLedgerUnary regseqratReadbackUnary consumerRow
  exact ⟨partialSumsUnary, scheduleUnary, tailLedgerUnary, regseqratReadbackUnary,
    consumerUnary, partialScheduleRow, consumerRow, pkgSig⟩

theorem FastConvergentSeriesCarrier_scoped_kernel_factorization [AskSetup] [PackageSetup]
    {series seq partialSums schedule tailLedger regReadback realSeal transports routes provenance
      nameCert consumerRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastConvergentSeriesCarrier series seq partialSums schedule tailLedger regReadback
        realSeal transports routes provenance nameCert bundle pkg ->
      FastConvergentSeriesTailBoundPacket series partialSums schedule tailLedger
        regReadback realSeal transports provenance nameCert bundle pkg ->
        Cont tailLedger regReadback consumerRead ->
          Cont realSeal provenance endpoint ->
            UnaryHistory schedule ∧ UnaryHistory tailLedger ∧ UnaryHistory regReadback ∧
              UnaryHistory realSeal ∧ UnaryHistory consumerRead ∧
                Cont schedule partialSums tailLedger ∧
                  Cont tailLedger regReadback consumerRead ∧
                    Cont realSeal provenance endpoint ∧
                      hsame tailLedger (append schedule partialSums) ∧
                        hsame realSeal (append tailLedger regReadback) ∧
                          PkgSig bundle provenance pkg := by
  intro carrier packet consumerRow endpointRow
  obtain ⟨_seriesUnary, _partialSumsUnary, scheduleUnary, regReadbackUnary,
    _realSealPacketUnary, _provenanceUnary, partialScheduleRow, _sealRow, _transportRow,
    _provenanceRow, pkgSig⟩ := packet
  obtain ⟨_carrierSeriesUnary, _seqUnary, _carrierPartialUnary, _carrierScheduleUnary,
    tailLedgerUnary, _carrierRegReadbackUnary, realSealUnary, _transportsUnary,
    _routesUnary, _nameCertUnary, _seriesRow, carrierScheduleRow, _carrierSealRow,
    _nameCertRow, tailSame, sealSame, _carrierPkgSig⟩ := carrier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed tailLedgerUnary regReadbackUnary consumerRow
  exact ⟨scheduleUnary, tailLedgerUnary, regReadbackUnary, realSealUnary, consumerUnary,
    carrierScheduleRow, consumerRow, endpointRow, tailSame, sealSame, pkgSig⟩

theorem FastConvergentSeriesCarrier_bridge_real_seal_consumer [AskSetup] [PackageSetup]
    {series seq partialSums schedule tailLedger regReadback realSeal transports routes provenance
      nameCert consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastConvergentSeriesCarrier series seq partialSums schedule tailLedger regReadback
        realSeal transports routes provenance nameCert bundle pkg ->
      FastConvergentSeriesTailBoundPacket series partialSums schedule tailLedger
        regReadback realSeal transports provenance nameCert bundle pkg ->
        Cont tailLedger regReadback consumerRead ->
          UnaryHistory schedule ∧ UnaryHistory tailLedger ∧ UnaryHistory regReadback ∧
            UnaryHistory realSeal ∧ UnaryHistory consumerRead ∧
              Cont schedule partialSums tailLedger ∧
                Cont tailLedger regReadback consumerRead ∧
                  hsame realSeal (append tailLedger regReadback) ∧
                    PkgSig bundle provenance pkg := by
  intro carrier packet consumerRow
  obtain ⟨_seriesUnary, _partialSumsUnary, scheduleUnary, regReadbackUnary,
    _realSealPacketUnary, _provenanceUnary, _partialScheduleRow, _packetSealRow,
    _transportRow, _provenanceRow, pkgSig⟩ := packet
  obtain ⟨_carrierSeriesUnary, _seqUnary, _carrierPartialUnary, _carrierScheduleUnary,
    tailLedgerUnary, _carrierRegReadbackUnary, realSealUnary, _transportsUnary,
    _routesUnary, _nameCertUnary, _seriesRow, carrierScheduleRow, _carrierSealRow,
    _nameCertRow, _tailSame, sealSame, _carrierPkgSig⟩ := carrier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed tailLedgerUnary regReadbackUnary consumerRow
  exact ⟨scheduleUnary, tailLedgerUnary, regReadbackUnary, realSealUnary, consumerUnary,
    carrierScheduleRow, consumerRow, sealSame, pkgSig⟩

theorem FastConvergentSeriesCarrier_public_tail_budget_export [AskSetup] [PackageSetup]
    {series seq partialSums schedule tailLedger regReadback realSeal transports routes provenance
      nameCert consumerRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastConvergentSeriesCarrier series seq partialSums schedule tailLedger regReadback
        realSeal transports routes provenance nameCert bundle pkg ->
      FastConvergentSeriesTailBoundPacket series partialSums schedule tailLedger
        regReadback realSeal transports provenance nameCert bundle pkg ->
        Cont tailLedger regReadback consumerRead ->
          Cont realSeal provenance endpoint ->
            PkgSig bundle endpoint pkg ->
              UnaryHistory series ∧ UnaryHistory partialSums ∧ UnaryHistory schedule ∧
                UnaryHistory tailLedger ∧ UnaryHistory regReadback ∧ UnaryHistory realSeal ∧
                  UnaryHistory consumerRead ∧ Cont series seq partialSums ∧
                    Cont schedule partialSums tailLedger ∧
                      Cont tailLedger regReadback consumerRead ∧
                        Cont realSeal provenance endpoint ∧
                          hsame tailLedger (append schedule partialSums) ∧
                            hsame realSeal (append tailLedger regReadback) ∧
                              PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg := by
  intro carrier packet consumerRow endpointRow endpointPkg
  obtain ⟨seriesUnary, partialSumsUnary, scheduleUnary, regReadbackUnary,
    _realSealPacketUnary, _provenanceUnary, _partialSchedulePacketRow, _packetSealRow,
    _transportRow, _provenanceRow, provenancePkg⟩ := packet
  obtain ⟨_carrierSeriesUnary, _seqUnary, _carrierPartialSumsUnary, _carrierScheduleUnary,
    tailLedgerUnary, _carrierRegReadbackUnary, realSealUnary, _transportsUnary, _routesUnary,
    _nameCertUnary, sourceRow, scheduleTailRow, _sealRow, _nameCertRow, tailSame, sealSame,
    _carrierPkgSig⟩ := carrier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed tailLedgerUnary regReadbackUnary consumerRow
  exact
    ⟨seriesUnary, partialSumsUnary, scheduleUnary, tailLedgerUnary, regReadbackUnary,
      realSealUnary, consumerUnary, sourceRow, scheduleTailRow, consumerRow, endpointRow,
      tailSame, sealSame, provenancePkg, endpointPkg⟩

theorem FastConvergentSeriesCarrier_bridge_completion_handoff [AskSetup] [PackageSetup]
    {series seq partialSums schedule tailLedger regReadback realSeal transports routes provenance
      nameCert consumerRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastConvergentSeriesCarrier series seq partialSums schedule tailLedger regReadback
        realSeal transports routes provenance nameCert bundle pkg ->
      FastConvergentSeriesTailBoundPacket series partialSums schedule tailLedger
        regReadback realSeal transports provenance nameCert bundle pkg ->
        Cont tailLedger regReadback consumerRead ->
          Cont realSeal provenance endpoint ->
            hsame realSeal consumerRead ∧ UnaryHistory consumerRead ∧
              UnaryHistory endpoint ∧ Cont tailLedger regReadback consumerRead ∧
                Cont realSeal provenance endpoint ∧ PkgSig bundle provenance pkg := by
  intro carrier packet consumerRow endpointRow
  obtain ⟨_seriesUnary, _seqUnary, _partialUnary, _scheduleUnary, tailLedgerUnary,
    _regReadbackUnary, realSealUnary, _transportsUnary, _routesUnary, _nameCertUnary,
    _seriesSeqRow, _scheduleTailRow, realSealRow, _nameCertRow, _tailSame, _sealSame,
    _carrierPkg⟩ := carrier
  obtain ⟨_packetSeriesUnary, _packetPartialUnary, _packetScheduleUnary, regReadbackUnary,
    _packetSealUnary, provenanceUnary, _packetTailRow, _packetSealRow, _packetTransportRow,
    _packetProvenanceRow, packetPkg⟩ := packet
  have sameConsumer : hsame realSeal consumerRead :=
    cont_deterministic realSealRow consumerRow
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed tailLedgerUnary regReadbackUnary consumerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed realSealUnary provenanceUnary endpointRow
  exact ⟨sameConsumer, consumerUnary, endpointUnary, consumerRow, endpointRow, packetPkg⟩

theorem FastConvergentSeriesCarrier_bridge_boundary_package [AskSetup] [PackageSetup]
    {series seq partialSums schedule tailLedger regReadback realSeal transports routes provenance
      nameCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastConvergentSeriesCarrier series seq partialSums schedule tailLedger regReadback
        realSeal transports routes provenance nameCert bundle pkg ->
      Cont realSeal provenance endpoint ->
        SemanticNameCert
          (fun row : BHist =>
            hsame row endpoint ∧ Cont realSeal provenance row ∧
              FastConvergentSeriesCarrier series seq partialSums schedule tailLedger regReadback
                realSeal transports routes provenance nameCert bundle pkg)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle provenance pkg)
          hsame := by
  intro carrier endpointCont
  have carrierProof := carrier
  obtain ⟨_seriesUnary, _seqUnary, _partialSumsUnary, _scheduleUnary, _tailLedgerUnary,
    _regReadbackUnary, _realSealUnary, _transportsUnary, _routesUnary, _nameCertUnary,
    _seriesSeqPartial, _schedulePartialTail, _tailReadbackSeal, _sealProvenanceName,
    _tailSame, _sealSame, pkgSig⟩ := carrier
  have sourceEndpoint :
      (fun row : BHist =>
        hsame row endpoint ∧ Cont realSeal provenance row ∧
          FastConvergentSeriesCarrier series seq partialSums schedule tailLedger regReadback
            realSeal transports routes provenance nameCert bundle pkg) endpoint := by
    exact ⟨hsame_refl endpoint, endpointCont, carrierProof⟩
  have core :
      NameCert
        (fun row : BHist =>
          hsame row endpoint ∧ Cont realSeal provenance row ∧
            FastConvergentSeriesCarrier series seq partialSums schedule tailLedger regReadback
              realSeal transports routes provenance nameCert bundle pkg)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro endpoint sourceEndpoint
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other same
        exact hsame_symm same
      equiv_trans := by
        intro row other third sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro row other same source
        have otherEndpoint : hsame other endpoint :=
          hsame_trans (hsame_symm same) source.left
        have otherCont : Cont realSeal provenance other :=
          cont_result_hsame_transport source.right.left same
        exact ⟨otherEndpoint, otherCont, source.right.right⟩
    }
  exact {
    core := core
    pattern_sound := by
      intro row source
      exact source.left
    ledger_sound := by
      intro row source
      exact ⟨source.left, pkgSig⟩
  }

theorem FastConvergentSeriesCarrier_public_export [AskSetup] [PackageSetup]
    {series seq partialSums schedule tailLedger regReadback realSeal transports routes provenance
      nameCert consumerRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastConvergentSeriesCarrier series seq partialSums schedule tailLedger regReadback
        realSeal transports routes provenance nameCert bundle pkg ->
      FastConvergentSeriesTailBoundPacket series partialSums schedule tailLedger
        regReadback realSeal transports provenance nameCert bundle pkg ->
        Cont tailLedger regReadback consumerRead ->
          Cont realSeal provenance endpoint ->
            PkgSig bundle endpoint pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row endpoint ∧ Cont realSeal provenance row ∧
                      FastConvergentSeriesCarrier series seq partialSums schedule tailLedger
                        regReadback realSeal transports routes provenance nameCert bundle pkg)
                  (fun row : BHist => hsame row endpoint)
                  (fun row : BHist => hsame row endpoint ∧ PkgSig bundle provenance pkg)
                  hsame ∧
                UnaryHistory series ∧ UnaryHistory partialSums ∧ UnaryHistory schedule ∧
                  UnaryHistory tailLedger ∧ UnaryHistory regReadback ∧ UnaryHistory realSeal ∧
                    UnaryHistory consumerRead ∧ UnaryHistory endpoint ∧
                      hsame realSeal consumerRead ∧ Cont tailLedger regReadback consumerRead ∧
                        Cont realSeal provenance endpoint ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle endpoint pkg := by
  intro carrier packet consumerRow endpointRow endpointPkg
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row endpoint ∧ Cont realSeal provenance row ∧
              FastConvergentSeriesCarrier series seq partialSums schedule tailLedger regReadback
                realSeal transports routes provenance nameCert bundle pkg)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle provenance pkg)
          hsame :=
    FastConvergentSeriesCarrier_bridge_boundary_package carrier endpointRow
  have publicRows :=
    FastConvergentSeriesCarrier_public_tail_budget_export carrier packet consumerRow endpointRow
      endpointPkg
  have handoff :=
    FastConvergentSeriesCarrier_bridge_completion_handoff carrier packet consumerRow endpointRow
  obtain ⟨seriesUnary, partialSumsUnary, scheduleUnary, tailLedgerUnary, regReadbackUnary,
    realSealUnary, consumerUnary, _seriesRow, _scheduleRow, _consumerRow, _endpointRow,
    _tailSame, _sealSame, provenancePkg, endpointPkg'⟩ := publicRows
  obtain ⟨sameRealConsumer, _handoffConsumerUnary, endpointUnary, _handoffConsumerRow,
    _handoffEndpointRow, _handoffPkg⟩ := handoff
  exact
    ⟨cert, seriesUnary, partialSumsUnary, scheduleUnary, tailLedgerUnary, regReadbackUnary,
      realSealUnary, consumerUnary, endpointUnary, sameRealConsumer, consumerRow, endpointRow,
      provenancePkg, endpointPkg'⟩

theorem FastConvergentSeriesCarrier_mature_boundary_package [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} {endpoint : BHist} :
    PkgSig bundle BHist.Empty pkg ->
      Cont BHist.Empty BHist.Empty endpoint ->
        SemanticNameCert
          (fun row : BHist =>
            hsame row endpoint ∧ Cont BHist.Empty BHist.Empty row ∧
              FastConvergentSeriesCarrier BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty bundle pkg)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle BHist.Empty pkg)
          hsame := by
  intro pkgSig endpointCont
  have zeroCarrier :
      FastConvergentSeriesCarrier BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        bundle pkg :=
    FastConvergentSeriesCarrier_constant_zero_seed pkgSig
  have sourceEndpoint :
      (fun row : BHist =>
        hsame row endpoint ∧ Cont BHist.Empty BHist.Empty row ∧
          FastConvergentSeriesCarrier BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            bundle pkg) endpoint := by
    exact ⟨hsame_refl endpoint, endpointCont, zeroCarrier⟩
  have core :
      NameCert
        (fun row : BHist =>
          hsame row endpoint ∧ Cont BHist.Empty BHist.Empty row ∧
            FastConvergentSeriesCarrier BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              bundle pkg)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro endpoint sourceEndpoint
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other same
        exact hsame_symm same
      equiv_trans := by
        intro row other third sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro row other same source
        have otherEndpoint : hsame other endpoint :=
          hsame_trans (hsame_symm same) source.left
        have otherCont : Cont BHist.Empty BHist.Empty other :=
          cont_result_hsame_transport source.right.left same
        exact ⟨otherEndpoint, otherCont, source.right.right⟩
    }
  exact {
    core := core
    pattern_sound := by
      intro row source
      exact source.left
    ledger_sound := by
      intro row source
      exact ⟨source.left, pkgSig⟩
  }

theorem FastConvergentSeriesTailBoundPacket_bridge_completion_handoff [AskSetup] [PackageSetup]
    {summand partialSums schedule tailLedger regseqratReadback sealRow transport provenance
      localCert consumerRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastConvergentSeriesTailBoundPacket summand partialSums schedule tailLedger
        regseqratReadback sealRow transport provenance localCert bundle pkg ->
      Cont tailLedger regseqratReadback consumerRead ->
        Cont sealRow provenance endpoint ->
          PkgSig bundle endpoint pkg ->
            hsame sealRow consumerRead ∧ UnaryHistory partialSums ∧ UnaryHistory schedule ∧
              UnaryHistory tailLedger ∧ UnaryHistory regseqratReadback ∧
                UnaryHistory consumerRead ∧ UnaryHistory endpoint ∧
                  Cont partialSums schedule tailLedger ∧
                    Cont tailLedger regseqratReadback consumerRead ∧
                      Cont sealRow provenance endpoint ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle endpoint pkg := by
  intro packet consumerRow endpointRow endpointPkg
  obtain ⟨_summandUnary, partialSumsUnary, scheduleUnary, regseqratReadbackUnary,
    _sealUnary, provenanceUnary, partialScheduleRow, sealRowCont, _transportRow,
    _provenanceRow, provenancePkg⟩ := packet
  have tailLedgerUnary : UnaryHistory tailLedger :=
    unary_cont_closed partialSumsUnary scheduleUnary partialScheduleRow
  have sameSealConsumer : hsame sealRow consumerRead :=
    cont_deterministic sealRowCont consumerRow
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed tailLedgerUnary regseqratReadbackUnary consumerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed _sealUnary provenanceUnary endpointRow
  exact
    ⟨sameSealConsumer, partialSumsUnary, scheduleUnary, tailLedgerUnary, regseqratReadbackUnary,
      consumerUnary, endpointUnary, partialScheduleRow, consumerRow, endpointRow, provenancePkg,
      endpointPkg⟩

theorem FastConvergentSeriesCarrier_cauchy_consumer_coverage [AskSetup] [PackageSetup]
    {series seq partialSums schedule tailLedger regReadback realSeal transports routes provenance
      nameCert consumerRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastConvergentSeriesCarrier series seq partialSums schedule tailLedger regReadback
        realSeal transports routes provenance nameCert bundle pkg ->
      FastConvergentSeriesTailBoundPacket series partialSums schedule tailLedger regReadback
        realSeal transports provenance nameCert bundle pkg ->
        Cont tailLedger regReadback consumerRead ->
          Cont realSeal provenance endpoint ->
            PkgSig bundle endpoint pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row endpoint ∧ Cont realSeal provenance row ∧
                      FastConvergentSeriesCarrier series seq partialSums schedule tailLedger
                        regReadback realSeal transports routes provenance nameCert bundle pkg)
                  (fun row : BHist => hsame row endpoint)
                  (fun row : BHist => hsame row endpoint ∧ PkgSig bundle provenance pkg)
                  hsame ∧
                UnaryHistory consumerRead ∧ UnaryHistory endpoint ∧
                  Cont tailLedger regReadback consumerRead ∧ Cont realSeal provenance endpoint ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg := by
  intro carrier packet consumerRow endpointRow endpointPkg
  have carrierProof := carrier
  obtain ⟨_seriesUnary, _seqUnary, _partialSumsUnary, _scheduleUnary, tailLedgerUnary,
    _regReadbackCarrierUnary, realSealUnary, _transportsUnary, _routesUnary,
    _nameCertCarrierUnary, _seriesSeqPartial, _schedulePartialTail, _tailReadbackSeal,
    _sealProvenanceName, _tailSame, _sealSame, _carrierPkg⟩ := carrier
  obtain ⟨_packetSeriesUnary, _packetPartialUnary, _packetScheduleUnary, regReadbackUnary,
    _packetSealUnary, provenanceUnary, _packetTailRow, _packetSealRow, _packetTransportRow,
    _packetProvenanceRow, provenancePkg⟩ := packet
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed tailLedgerUnary regReadbackUnary consumerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed realSealUnary provenanceUnary endpointRow
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row endpoint ∧ Cont realSeal provenance row ∧
              FastConvergentSeriesCarrier series seq partialSums schedule tailLedger
                regReadback realSeal transports routes provenance nameCert bundle pkg)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle provenance pkg)
          hsame :=
    FastConvergentSeriesCarrier_bridge_boundary_package carrierProof endpointRow
  exact
    ⟨cert, consumerUnary, endpointUnary, consumerRow, endpointRow, provenancePkg, endpointPkg⟩

end BEDC.Derived.FastConvergentSeriesUp
