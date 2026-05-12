import BEDC.Derived.RealUp.Core

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RegseqratFiniteWindowDyadicObservationCoverage
    {s t : Nat -> BHist} {n : Nat}
    {anchor bound offset selected leftObs rightObs leftWindow rightWindow : BHist} :
    RealStreamClassifier s t ->
    UnaryHistory anchor ->
    UnaryHistory offset ->
    UnaryHistory bound ->
    Cont anchor offset selected ->
    hsame (s n) leftObs ->
    hsame (t n) rightObs ->
    Cont anchor bound leftWindow ->
    Cont anchor bound rightWindow ->
    PositiveUnaryDenominator leftObs ->
    PositiveUnaryDenominator rightObs ->
    UnaryHistory selected ∧ UnaryHistory leftWindow ∧ UnaryHistory rightWindow ∧
      hsame (s n) leftObs ∧ hsame (t n) rightObs ∧
        PositiveUnaryDenominator leftObs ∧ PositiveUnaryDenominator rightObs := by
  intro _classified anchorUnary offsetUnary boundUnary selectedCont leftObsSame rightObsSame
    leftWindowCont rightWindowCont leftPositive rightPositive
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed anchorUnary offsetUnary selectedCont
  have leftWindowUnary : UnaryHistory leftWindow :=
    unary_cont_closed anchorUnary boundUnary leftWindowCont
  have rightWindowUnary : UnaryHistory rightWindow :=
    unary_cont_closed anchorUnary boundUnary rightWindowCont
  exact And.intro selectedUnary
    (And.intro leftWindowUnary
      (And.intro rightWindowUnary
        (And.intro leftObsSame
          (And.intro rightObsSame
            (And.intro leftPositive rightPositive)))))

end BEDC.Derived.RealUp
