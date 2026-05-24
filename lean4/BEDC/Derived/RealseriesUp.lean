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

end BEDC.Derived.RealseriesUp
