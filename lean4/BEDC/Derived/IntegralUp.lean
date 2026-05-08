import BEDC.Derived.ContourIntegralUp
import BEDC.Derived.MeasureUp
import BEDC.Derived.RealUp.Core
import BEDC.Derived.RatUp.HistoryClassifier
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
open BEDC.Derived.RealUp
open BEDC.Derived.RatUp

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

def IntegralVisibleCarrierRow
    (measure contour integrand value measureContour integrandValue row : BHist) : Prop :=
  MeasureZeroBHistCarrier measure ∧
    PLContour contour ∧
      UnaryHistory integrand ∧
        RealConstantHistoryCarrier value ∧
          Cont measure contour measureContour ∧
            Cont integrand value integrandValue ∧
              Cont measureContour integrandValue row

theorem IntegralVisibleCarrierRow_readback
    {measure contour integrand value measureContour integrandValue row : BHist} :
    IntegralVisibleCarrierRow measure contour integrand value measureContour integrandValue row ->
      MeasureZeroBHistCarrier measure ∧
        PLContour contour ∧
          UnaryHistory integrand ∧
            RealConstantHistoryCarrier value ∧
              Cont measureContour integrandValue row ∧ UnaryHistory row := by
  intro carrier
  have measureUnary : UnaryHistory measure := unary_transport unary_empty (hsame_symm carrier.left)
  let rec contourUnary : {gamma : BHist} -> PLContour gamma -> UnaryHistory gamma
    | _, PLContour.segment segment =>
        by
          cases PLContourSegment_unary_result segment with
          | intro _z0 rest =>
              cases rest with
              | intro _z1 data =>
                  exact data.right.right.right
    | _, PLContour.concat leftContour rightContour join =>
        unary_cont_closed (contourUnary leftContour) (contourUnary rightContour) join
  have contourCarrier : UnaryHistory contour := contourUnary carrier.right.left
  have measureContourCarrier : UnaryHistory measureContour :=
    unary_cont_closed measureUnary contourCarrier carrier.right.right.right.right.left
  have valueUnary : UnaryHistory value := by
    cases carrier.right.right.right.left with
    | intro valueTail valueData =>
      have valueTailUnary : UnaryHistory valueTail :=
        (PositiveUnaryDenominator_unary_and_nonempty
          (RatHistoryCarrier_iff_positive_denominator.mp valueData.right)).left
      exact unary_transport (unary_e1_closed valueTailUnary) (hsame_symm valueData.left)
  have integrandValueCarrier : UnaryHistory integrandValue :=
    unary_cont_closed carrier.right.right.left valueUnary carrier.right.right.right.right.right.left
  have rowUnary : UnaryHistory row :=
    unary_cont_closed measureContourCarrier integrandValueCarrier
      carrier.right.right.right.right.right.right
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro carrier.right.right.left
        (And.intro carrier.right.right.right.left
          (And.intro carrier.right.right.right.right.right.right rowUnary))))

theorem IntegralVisibleCarrierRow_measure_respecting_classifier
    {measure contour integrand value measureContour integrandValue row measure' contour'
      integrand' value' measureContour' integrandValue' row' : BHist} :
    IntegralVisibleCarrierRow measure contour integrand value measureContour integrandValue row ->
      IntegralVisibleCarrierRow measure' contour' integrand' value' measureContour'
          integrandValue' row' ->
        hsame measure measure' -> hsame contour contour' -> hsame integrand integrand' ->
          hsame value value' ->
            MeasureZeroBHistClassifier measure measure' ∧
              Cont measureContour integrandValue row ∧
                Cont measureContour' integrandValue' row' ∧
                  hsame measureContour measureContour' ∧
                    hsame integrandValue integrandValue' ∧ hsame row row' := by
  intro leftCarrier rightCarrier sameMeasure sameContour sameIntegrand sameValue
  have measureClassified : MeasureZeroBHistClassifier measure measure' :=
    And.intro leftCarrier.left (And.intro rightCarrier.left sameMeasure)
  have leftMeasureContour : Cont measure contour measureContour :=
    leftCarrier.right.right.right.right.left
  have rightMeasureContour : Cont measure' contour' measureContour' :=
    rightCarrier.right.right.right.right.left
  have sameMeasureContour : hsame measureContour measureContour' :=
    cont_respects_hsame sameMeasure sameContour leftMeasureContour rightMeasureContour
  have leftIntegrandValue : Cont integrand value integrandValue :=
    leftCarrier.right.right.right.right.right.left
  have rightIntegrandValue : Cont integrand' value' integrandValue' :=
    rightCarrier.right.right.right.right.right.left
  have sameIntegrandValue : hsame integrandValue integrandValue' :=
    cont_respects_hsame sameIntegrand sameValue leftIntegrandValue rightIntegrandValue
  have leftRow : Cont measureContour integrandValue row :=
    leftCarrier.right.right.right.right.right.right
  have rightRow : Cont measureContour' integrandValue' row' :=
    rightCarrier.right.right.right.right.right.right
  have sameRow : hsame row row' :=
    cont_respects_hsame sameMeasureContour sameIntegrandValue leftRow rightRow
  exact And.intro measureClassified
    (And.intro leftRow
      (And.intro rightRow
        (And.intro sameMeasureContour (And.intro sameIntegrandValue sameRow))))

theorem IntegralVisibleCarrierRow_measure_prefix_scope (events values : Nat -> BHist)
    {measure contour integrand value measureContour integrandValue row : BHist} :
    (forall n : Nat, MeasureZeroBHistClassifier (events n) (values n)) ->
      IntegralVisibleCarrierRow measure contour integrand value measureContour integrandValue row ->
        forall n : Nat,
          MeasureZeroBHistClassifier (MeasureZeroBHistPrefix events n)
              (MeasureZeroBHistPrefix values n) ∧
            Cont (MeasureZeroBHistPrefix events n) (events n)
              (MeasureZeroBHistPrefix events (Nat.succ n)) ∧
              Cont (MeasureZeroBHistPrefix values n) (values n)
                (MeasureZeroBHistPrefix values (Nat.succ n)) ∧
                MeasureZeroBHistCarrier measure ∧ PLContour contour ∧ UnaryHistory row := by
  intro pointwise carrier n
  have eventsZero : forall m : Nat, MeasureZeroBHistCarrier (events m) := by
    intro m
    exact (pointwise m).left
  have valuesZero : forall m : Nat, MeasureZeroBHistCarrier (values m) := by
    intro m
    exact (pointwise m).right.left
  have eventStep :=
    (MeasureZeroBHist_sigma_additivity events eventsZero n).left
  have valueStep :=
    (MeasureZeroBHist_sigma_additivity values valuesZero n).left
  have prefixClassified :=
    MeasureZeroBHistPrefix_classifier_stability events values pointwise n
  have readback := IntegralVisibleCarrierRow_readback carrier
  exact And.intro prefixClassified
    (And.intro eventStep
      (And.intro valueStep
        (And.intro readback.left
          (And.intro readback.right.left readback.right.right.right.right.right))))

theorem IntegralVisibleCarrierRow_classifier_boundary_transport
    {measure contour integrand value measureContour integrandValue row measure' contour'
      integrand' value' measureContour' integrandValue' row' : BHist} :
    IntegralVisibleCarrierRow measure contour integrand value measureContour integrandValue row ->
      IntegralVisibleCarrierRow measure' contour' integrand' value' measureContour'
        integrandValue' row' ->
        hsame measureContour measureContour' ->
          hsame integrandValue integrandValue' ->
            hsame row row' ∧ UnaryHistory row ∧ UnaryHistory row' := by
  intro leftRow rightRow sameMeasureContour sameIntegrandValue
  have leftReadback := IntegralVisibleCarrierRow_readback leftRow
  have rightReadback := IntegralVisibleCarrierRow_readback rightRow
  have sameRow : hsame row row' :=
    cont_respects_hsame sameMeasureContour sameIntegrandValue
      leftReadback.right.right.right.right.left
      rightReadback.right.right.right.right.left
  exact And.intro sameRow
    (And.intro leftReadback.right.right.right.right.right
      rightReadback.right.right.right.right.right)

theorem IntegralPublicNameCert_surface [AskSetup] [PackageSetup]
    {measure contour integrand value measureContour integrandValue row row' : BHist} :
    IntegralVisibleCarrierRow measure contour integrand value measureContour integrandValue row ->
      hsame row row' ->
        UnaryHistory row' ∧ MeasureZeroBHistCarrier measure ∧ PLContour contour ∧
          UnaryHistory integrand ∧ RealConstantHistoryCarrier value ∧
            Cont measureContour integrandValue row := by
  intro carrier sameRow
  have readback := IntegralVisibleCarrierRow_readback carrier
  have rowUnary' : UnaryHistory row' :=
    unary_transport readback.right.right.right.right.right sameRow
  exact And.intro rowUnary'
    (And.intro readback.left
      (And.intro readback.right.left
        (And.intro readback.right.right.left
          (And.intro readback.right.right.right.left readback.right.right.right.right.left))))

end BEDC.Derived.IntegralUp
