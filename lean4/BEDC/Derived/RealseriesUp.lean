import BEDC.FKernel.Package.Core
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RealseriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealSeriesRootCauchyProductSurface [AskSetup] [PackageSetup]
    (term «partial» window readback dyadic threshold transport replay provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory term ∧ UnaryHistory «partial» ∧ UnaryHistory window ∧
    UnaryHistory readback ∧ UnaryHistory dyadic ∧ UnaryHistory threshold ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory cert ∧ Cont readback dyadic threshold ∧ PkgSig bundle provenance pkg

theorem RealSeriesRootCauchyTailBudget [AskSetup] [PackageSetup]
    {term «partial» window readback dyadic threshold transport replay provenance cert
      productRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSeriesRootCauchyProductSurface term «partial» window readback dyadic threshold
        transport replay provenance cert bundle pkg →
      Cont threshold cert productRead →
        PkgSig bundle productRead pkg →
          UnaryHistory term ∧ UnaryHistory «partial» ∧ UnaryHistory window ∧
            UnaryHistory readback ∧ UnaryHistory dyadic ∧ UnaryHistory threshold ∧
              UnaryHistory productRead ∧ Cont readback dyadic threshold ∧
                Cont threshold cert productRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle productRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier thresholdCertRead productReadPkg
  obtain ⟨termUnary, partialUnary, windowUnary, readbackUnary, dyadicUnary,
    thresholdUnary, _transportUnary, _replayUnary, _provenanceUnary, certUnary,
    readbackDyadicThreshold, provenancePkg⟩ := carrier
  have productReadUnary : UnaryHistory productRead :=
    unary_cont_closed thresholdUnary certUnary thresholdCertRead
  exact
    ⟨termUnary, partialUnary, windowUnary, readbackUnary, dyadicUnary, thresholdUnary,
      productReadUnary, readbackDyadicThreshold, thresholdCertRead, provenancePkg,
      productReadPkg⟩

theorem RealSeriesRootUnblockCarrier [AskSetup] [PackageSetup]
    {term «partial» window readback dyadic threshold transport replay provenance cert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSeriesRootCauchyProductSurface term «partial» window readback dyadic threshold
        transport replay provenance cert bundle pkg →
      UnaryHistory term ∧ UnaryHistory «partial» ∧ UnaryHistory window ∧
        UnaryHistory readback ∧ UnaryHistory dyadic ∧ UnaryHistory threshold ∧
          UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
            UnaryHistory cert ∧ Cont readback dyadic threshold ∧
              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier
  exact carrier

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

theorem RealSeriesRegSeqRatTailObligation [AskSetup] [PackageSetup]
    {term «partial» window readback dyadic threshold transport replay provenance cert
      qtail endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSeriesRootCauchyProductSurface term «partial» window readback dyadic threshold
        transport replay provenance cert bundle pkg →
      Cont readback dyadic qtail →
        Cont qtail threshold endpoint →
          PkgSig bundle endpoint pkg →
            UnaryHistory readback ∧ UnaryHistory dyadic ∧ UnaryHistory qtail ∧
              UnaryHistory threshold ∧ UnaryHistory endpoint ∧ Cont readback dyadic qtail ∧
                Cont qtail threshold endpoint ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier readbackDyadicTail tailThresholdEndpoint endpointPkg
  obtain ⟨_termUnary, _partialUnary, _windowUnary, readbackUnary, dyadicUnary,
    thresholdUnary, _transportUnary, _replayUnary, _provenanceUnary, _certUnary,
    _readbackDyadicThreshold, provenancePkg⟩ := carrier
  have qtailUnary : UnaryHistory qtail :=
    unary_cont_closed readbackUnary dyadicUnary readbackDyadicTail
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed qtailUnary thresholdUnary tailThresholdEndpoint
  exact
    ⟨readbackUnary, dyadicUnary, qtailUnary, thresholdUnary, endpointUnary,
      readbackDyadicTail, tailThresholdEndpoint, provenancePkg, endpointPkg⟩

theorem RealSeriesPartialSumWindowRoute [AskSetup] [PackageSetup]
    {term «partial» window readback dyadic threshold transport replay provenance cert
      partialWindow readbackWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSeriesRootCauchyProductSurface term «partial» window readback dyadic threshold
        transport replay provenance cert bundle pkg →
      Cont «partial» window partialWindow →
        Cont partialWindow readback readbackWindow →
          PkgSig bundle readbackWindow pkg →
            UnaryHistory «partial» ∧ UnaryHistory window ∧ UnaryHistory partialWindow ∧
              UnaryHistory readback ∧ UnaryHistory readbackWindow ∧
                Cont «partial» window partialWindow ∧
                  Cont partialWindow readback readbackWindow ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle readbackWindow pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier partialWindowRoute readbackWindowRoute readbackWindowPkg
  obtain ⟨_termUnary, partialUnary, windowUnary, readbackUnary, _dyadicUnary,
    _thresholdUnary, _transportUnary, _replayUnary, _provenanceUnary, _certUnary,
    _readbackDyadicThreshold, provenancePkg⟩ := carrier
  have partialWindowUnary : UnaryHistory partialWindow :=
    unary_cont_closed partialUnary windowUnary partialWindowRoute
  have readbackWindowUnary : UnaryHistory readbackWindow :=
    unary_cont_closed partialWindowUnary readbackUnary readbackWindowRoute
  exact
    ⟨partialUnary, windowUnary, partialWindowUnary, readbackUnary, readbackWindowUnary,
      partialWindowRoute, readbackWindowRoute, provenancePkg, readbackWindowPkg⟩

theorem RealSeriesNonescapeBoundary [AskSetup] [PackageSetup]
    {term «partial» window readback dyadic threshold transport replay provenance cert
      endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSeriesRootCauchyProductSurface term «partial» window readback dyadic threshold
        transport replay provenance cert bundle pkg →
      Cont threshold cert endpointRead →
        PkgSig bundle endpointRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row term ∨ hsame row «partial» ∨ hsame row window ∨
                  hsame row readback ∨ hsame row dyadic ∨ hsame row threshold ∨
                    hsame row endpointRead)
              (fun row : BHist =>
                hsame row term ∨ hsame row «partial» ∨ hsame row window ∨
                  hsame row readback ∨ hsame row dyadic ∨ hsame row threshold ∨
                    hsame row endpointRead)
              (fun row : BHist =>
                PkgSig bundle endpointRead pkg ∧
                  (hsame row term ∨ hsame row «partial» ∨ hsame row window ∨
                    hsame row readback ∨ hsame row dyadic ∨ hsame row threshold ∨
                      hsame row endpointRead))
              hsame ∧
            UnaryHistory endpointRead ∧ Cont readback dyadic threshold ∧
              Cont threshold cert endpointRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro carrier thresholdCertEndpoint endpointPkg
  obtain ⟨_termUnary, _partialUnary, _windowUnary, readbackUnary, dyadicUnary,
    thresholdUnary, _transportUnary, _replayUnary, _provenanceUnary, certUnary,
    readbackDyadicThreshold, provenancePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed thresholdUnary certUnary thresholdCertEndpoint
  have sourceEndpoint :
      (fun row : BHist =>
        hsame row term ∨ hsame row «partial» ∨ hsame row window ∨
          hsame row readback ∨ hsame row dyadic ∨ hsame row threshold ∨
            hsame row endpointRead) endpointRead := by
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl endpointRead))))))
  have certData :
      SemanticNameCert
        (fun row : BHist =>
          hsame row term ∨ hsame row «partial» ∨ hsame row window ∨
            hsame row readback ∨ hsame row dyadic ∨ hsame row threshold ∨
              hsame row endpointRead)
        (fun row : BHist =>
          hsame row term ∨ hsame row «partial» ∨ hsame row window ∨
            hsame row readback ∨ hsame row dyadic ∨ hsame row threshold ∨
              hsame row endpointRead)
        (fun row : BHist =>
          PkgSig bundle endpointRead pkg ∧
            (hsame row term ∨ hsame row «partial» ∨ hsame row window ∨
              hsame row readback ∨ hsame row dyadic ∨ hsame row threshold ∨
                hsame row endpointRead))
        hsame := {
    core := {
      carrier_inhabited := Exists.intro endpointRead sourceEndpoint
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _other same source
        cases same
        exact source
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact ⟨endpointPkg, source⟩
  }
  exact
    ⟨certData, endpointUnary, readbackDyadicThreshold, thresholdCertEndpoint, provenancePkg,
      endpointPkg⟩

end BEDC.Derived.RealseriesUp
