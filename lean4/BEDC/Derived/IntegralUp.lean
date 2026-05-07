import BEDC.Derived.MeasureUp
import BEDC.Derived.ContourIntegralUp

namespace BEDC.Derived.IntegralUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.MeasureUp
open BEDC.Derived.ContourIntegralUp

def IntegralVisibleCarrier
    (measure integrand contour endpoint total : BHist) : Prop :=
  MeasureZeroBHistCarrier measure ∧ UnaryHistory integrand ∧ PLContour contour ∧
    Cont measure integrand endpoint ∧ Cont endpoint contour total

theorem IntegralFunctionCarrier_obligation {measure integrand contour endpoint total : BHist} :
    MeasureZeroBHistCarrier measure -> UnaryHistory integrand -> PLContour contour ->
      Cont measure integrand endpoint -> Cont endpoint contour total ->
        IntegralVisibleCarrier measure integrand contour endpoint total ∧ UnaryHistory endpoint := by
  intro measureCarrier integrandUnary contourCarrier measureIntegrand endpointContour
  have measureUnary : UnaryHistory measure :=
    unary_transport_symm unary_empty measureCarrier
  exact And.intro
    (And.intro measureCarrier
      (And.intro integrandUnary
        (And.intro contourCarrier
          (And.intro measureIntegrand endpointContour))))
    (unary_cont_closed measureUnary integrandUnary measureIntegrand)

end BEDC.Derived.IntegralUp
