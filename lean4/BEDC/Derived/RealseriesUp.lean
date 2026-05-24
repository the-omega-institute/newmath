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

end BEDC.Derived.RealseriesUp
