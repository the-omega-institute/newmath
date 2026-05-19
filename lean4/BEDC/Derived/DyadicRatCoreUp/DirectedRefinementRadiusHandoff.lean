import BEDC.Derived.DyadicRatCoreUp

namespace BEDC.Derived.DyadicRatCoreUp

open BEDC.Derived.RatUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicRatCoreCarrier_directed_refinement_radius_handoff [AskSetup] [PackageSetup]
    {m0 e0 l0 p0 m1 e1 l1 p1 common leftScale rightScale scaledLeft scaledRight
      classifierWindow radiusWindow handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicRatCoreCarrier m0 e0 l0 p0 →
      DyadicRatCoreCarrier m1 e1 l1 p1 →
        PositiveUnaryDenominator common →
          Cont e0 common leftScale →
            Cont e1 common rightScale →
              Cont m0 leftScale scaledLeft →
                Cont m1 rightScale scaledRight →
                  RatHistoryClassifier scaledLeft scaledRight →
                    Cont scaledLeft scaledRight classifierWindow →
                      Cont classifierWindow common radiusWindow →
                        Cont radiusWindow p0 handoff →
                          PkgSig bundle handoff pkg →
                            PositiveUnaryDenominator common ∧ UnaryHistory classifierWindow ∧
                              UnaryHistory radiusWindow ∧ UnaryHistory handoff ∧
                                Cont classifierWindow common radiusWindow ∧
                                  Cont radiusWindow p0 handoff ∧
                                    PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig RatHistoryClassifier
  intro carrier0 carrier1 commonPositive e0CommonLeftScale e1CommonRightScale
    m0LeftScaleScaledLeft m1RightScaleScaledRight _classified scaledClassifierWindow
    classifierCommonRadius radiusProvenanceHandoff handoffPkg
  have commonUnary : UnaryHistory common :=
    (PositiveUnaryDenominator_unary_and_nonempty commonPositive).left
  have e0Unary : UnaryHistory e0 :=
    (PositiveUnaryDenominator_unary_and_nonempty carrier0.right.left).left
  have e1Unary : UnaryHistory e1 :=
    (PositiveUnaryDenominator_unary_and_nonempty carrier1.right.left).left
  have m0Unary : UnaryHistory m0 :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp carrier0.left)).left
  have m1Unary : UnaryHistory m1 :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp carrier1.left)).left
  have leftScaleUnary : UnaryHistory leftScale :=
    unary_cont_closed e0Unary commonUnary e0CommonLeftScale
  have rightScaleUnary : UnaryHistory rightScale :=
    unary_cont_closed e1Unary commonUnary e1CommonRightScale
  have scaledLeftUnary : UnaryHistory scaledLeft :=
    unary_cont_closed m0Unary leftScaleUnary m0LeftScaleScaledLeft
  have scaledRightUnary : UnaryHistory scaledRight :=
    unary_cont_closed m1Unary rightScaleUnary m1RightScaleScaledRight
  have classifierWindowUnary : UnaryHistory classifierWindow :=
    unary_cont_closed scaledLeftUnary scaledRightUnary scaledClassifierWindow
  have radiusWindowUnary : UnaryHistory radiusWindow :=
    unary_cont_closed classifierWindowUnary commonUnary classifierCommonRadius
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed radiusWindowUnary carrier0.right.right.left radiusProvenanceHandoff
  exact
    ⟨commonPositive, classifierWindowUnary, radiusWindowUnary, handoffUnary,
      classifierCommonRadius, radiusProvenanceHandoff, handoffPkg⟩

end BEDC.Derived.DyadicRatCoreUp
