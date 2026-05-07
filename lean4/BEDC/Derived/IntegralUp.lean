import BEDC.Derived.ContourIntegralUp
import BEDC.Derived.MeasureUp
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.IntegralUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.ContourIntegralUp
open BEDC.Derived.MeasureUp

theorem IntegralMeasureRespectingClassifier_obligation [AskSetup] [PackageSetup]
    {measure measure' contour contour' integrand integrand' endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg pkg' : Pkg} :
    MeasureZeroBHistClassifier measure measure' -> PLContour contour -> PLContour contour' ->
      hsame contour contour' -> UnaryHistory integrand -> UnaryHistory integrand' ->
        hsame integrand integrand' -> TokIntro bundle measure pkg ->
          TokIntro bundle measure' pkg' -> Cont measure integrand endpoint ->
            Cont measure' integrand' endpoint' ->
              MeasureZeroBHistClassifier measure measure' ∧ hsame contour contour' ∧
                hsame endpoint endpoint' ∧ psame bundle pkg pkg' := by
  intro measureRows _contourRow _contourRow' sameContour _integrandUnary _integrandUnary'
    sameIntegrand token token' endpointRow endpointRow'
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame measureRows.right.right sameIntegrand endpointRow endpointRow'
  have packageSame : psame bundle pkg pkg' :=
    psame.intro token token' measureRows.right.right
  exact ⟨measureRows, sameContour, endpointSame, packageSame⟩

theorem IntegralOperationStabilityLedger_obligation [AskSetup] [PackageSetup]
    {measure integrand endpoint endpoint' partition approx convergence : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MeasureZeroBHistCarrier measure -> UnaryHistory integrand -> TokIntro bundle measure pkg ->
      Cont measure integrand endpoint -> hsame endpoint endpoint' ->
        Cont partition approx convergence -> hsame convergence BHist.Empty ->
          UnaryHistory endpoint' ∧ hsame partition BHist.Empty ∧ hsame approx BHist.Empty ∧
            (∃ sourcePkg : Pkg, TokIntro bundle measure sourcePkg) ∧
              Cont measure integrand endpoint ∧ hsame endpoint endpoint' := by
  intro measureCarrier integrandUnary token endpointRow sameEndpoint hiddenLedger convergenceEmpty
  have measureUnary : UnaryHistory measure :=
    unary_transport unary_empty (hsame_symm measureCarrier)
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed measureUnary integrandUnary endpointRow
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport endpointUnary sameEndpoint
  have hiddenRows : partition = BHist.Empty ∧ approx = BHist.Empty :=
    cont_empty_result_inversion (cont_result_hsame_transport hiddenLedger convergenceEmpty)
  exact ⟨endpointUnary', hiddenRows.left, hiddenRows.right, Exists.intro pkg token, endpointRow,
    sameEndpoint⟩

end BEDC.Derived.IntegralUp
