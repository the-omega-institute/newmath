import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RealseriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealSeriesRootCauchyProductSurface [AskSetup] [PackageSetup]
    (term «partial» window readback dyadic threshold transport replay provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory term ∧ UnaryHistory «partial» ∧ UnaryHistory window ∧
    UnaryHistory readback ∧ UnaryHistory dyadic ∧ UnaryHistory threshold ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory cert ∧ Cont readback dyadic threshold ∧ PkgSig bundle provenance pkg

theorem RealSeriesRootProductTailBudget [AskSetup] [PackageSetup]
    {term «partial» window readback dyadic threshold transport replay provenance cert budget : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSeriesRootCauchyProductSurface term «partial» window readback dyadic threshold transport
        replay provenance cert bundle pkg →
      Cont «partial» window budget →
        PkgSig bundle budget pkg →
          UnaryHistory «partial» ∧ UnaryHistory window ∧ UnaryHistory budget ∧
            UnaryHistory readback ∧ UnaryHistory dyadic ∧ UnaryHistory threshold ∧
              Cont «partial» window budget ∧ Cont readback dyadic threshold ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle budget pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier partialWindowBudget budgetPkg
  obtain ⟨_termUnary, partialUnary, windowUnary, readbackUnary, dyadicUnary,
    thresholdUnary, _transportUnary, _replayUnary, _provenanceUnary, _certUnary,
    readbackDyadicThreshold, provenancePkg⟩ := carrier
  have budgetUnary : UnaryHistory budget :=
    unary_cont_closed partialUnary windowUnary partialWindowBudget
  exact
    ⟨partialUnary, windowUnary, budgetUnary, readbackUnary, dyadicUnary, thresholdUnary,
      partialWindowBudget, readbackDyadicThreshold, provenancePkg, budgetPkg⟩

theorem RealSeries_uniform_cauchy_obligation [AskSetup] [PackageSetup]
    {term «partial» window readback dyadic threshold transport replay provenance cert
      uniformTail uniformSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSeriesRootCauchyProductSurface term «partial» window readback dyadic threshold
        transport replay provenance cert bundle pkg →
      Cont «partial» window uniformTail →
        Cont uniformTail dyadic uniformSeal →
          PkgSig bundle uniformSeal pkg →
            UnaryHistory term ∧ UnaryHistory «partial» ∧ UnaryHistory window ∧
              UnaryHistory uniformTail ∧ UnaryHistory dyadic ∧ UnaryHistory uniformSeal ∧
                Cont «partial» window uniformTail ∧ Cont uniformTail dyadic uniformSeal ∧
                  Cont readback dyadic threshold ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle uniformSeal pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier partialWindowTail tailDyadicSeal uniformSealPkg
  obtain ⟨termUnary, partialUnary, windowUnary, readbackUnary, dyadicUnary,
    _thresholdUnary, _transportUnary, _replayUnary, _provenanceUnary, _certUnary,
    readbackDyadicThreshold, provenancePkg⟩ := carrier
  have uniformTailUnary : UnaryHistory uniformTail :=
    unary_cont_closed partialUnary windowUnary partialWindowTail
  have uniformSealUnary : UnaryHistory uniformSeal :=
    unary_cont_closed uniformTailUnary dyadicUnary tailDyadicSeal
  exact
    ⟨termUnary, partialUnary, windowUnary, uniformTailUnary, dyadicUnary, uniformSealUnary,
      partialWindowTail, tailDyadicSeal, readbackDyadicThreshold, provenancePkg,
      uniformSealPkg⟩

theorem RealSeries_cauchy_majorant_obligation [AskSetup] [PackageSetup]
    {term «partial» window readback dyadic threshold transport replay provenance cert
      majorant majorantSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSeriesRootCauchyProductSurface term «partial» window readback dyadic threshold
        transport replay provenance cert bundle pkg →
      Cont readback dyadic majorant →
        Cont majorant threshold majorantSeal →
          PkgSig bundle majorantSeal pkg →
            UnaryHistory term ∧ UnaryHistory readback ∧ UnaryHistory dyadic ∧
              UnaryHistory threshold ∧ UnaryHistory majorant ∧
                UnaryHistory majorantSeal ∧ Cont readback dyadic majorant ∧
                  Cont majorant threshold majorantSeal ∧ Cont readback dyadic threshold ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle majorantSeal pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier readbackDyadicMajorant majorantThresholdSeal majorantSealPkg
  obtain ⟨termUnary, _partialUnary, _windowUnary, readbackUnary, dyadicUnary,
    thresholdUnary, _transportUnary, _replayUnary, _provenanceUnary, _certUnary,
    readbackDyadicThreshold, provenancePkg⟩ := carrier
  have majorantUnary : UnaryHistory majorant :=
    unary_cont_closed readbackUnary dyadicUnary readbackDyadicMajorant
  have majorantSealUnary : UnaryHistory majorantSeal :=
    unary_cont_closed majorantUnary thresholdUnary majorantThresholdSeal
  exact
    ⟨termUnary, readbackUnary, dyadicUnary, thresholdUnary, majorantUnary,
      majorantSealUnary, readbackDyadicMajorant, majorantThresholdSeal,
      readbackDyadicThreshold, provenancePkg, majorantSealPkg⟩

theorem RealSeries_partial_sum_ledger_nonescape [AskSetup] [PackageSetup]
    {term «partial» window readback dyadic threshold transport replay provenance cert
      partialWindow ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSeriesRootCauchyProductSurface term «partial» window readback dyadic threshold
        transport replay provenance cert bundle pkg →
      Cont term «partial» partialWindow →
        Cont partialWindow replay ledger →
          PkgSig bundle ledger pkg →
            UnaryHistory term ∧ UnaryHistory «partial» ∧ UnaryHistory partialWindow ∧
              UnaryHistory replay ∧ UnaryHistory ledger ∧ Cont term «partial» partialWindow ∧
                Cont partialWindow replay ledger ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle ledger pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier termPartialWindow partialWindowReplayLedger ledgerPkg
  obtain ⟨termUnary, partialUnary, _windowUnary, _readbackUnary, _dyadicUnary,
    _thresholdUnary, _transportUnary, replayUnary, _provenanceUnary, _certUnary,
    _readbackDyadicThreshold, provenancePkg⟩ := carrier
  have partialWindowUnary : UnaryHistory partialWindow :=
    unary_cont_closed termUnary partialUnary termPartialWindow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed partialWindowUnary replayUnary partialWindowReplayLedger
  exact
    ⟨termUnary, partialUnary, partialWindowUnary, replayUnary, ledgerUnary,
      termPartialWindow, partialWindowReplayLedger, provenancePkg, ledgerPkg⟩

end BEDC.Derived.RealseriesUp
