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

end BEDC.Derived.FastConvergentSeriesUp
