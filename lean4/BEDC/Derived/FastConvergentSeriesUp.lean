import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FastConvergentSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

def FastConvergentSeriesTailBoundPacket [AskSetup] [PackageSetup]
    (summand partialSums schedule tailLedger regseqratReadback «seal» transport provenance
      localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory summand ∧ UnaryHistory partialSums ∧ UnaryHistory schedule ∧
    UnaryHistory regseqratReadback ∧ UnaryHistory «seal» ∧ UnaryHistory provenance ∧
      Cont partialSums schedule tailLedger ∧ Cont tailLedger regseqratReadback «seal» ∧
        Cont summand tailLedger transport ∧ Cont transport localCert provenance ∧
          PkgSig bundle provenance pkg

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

end BEDC.Derived.FastConvergentSeriesUp
