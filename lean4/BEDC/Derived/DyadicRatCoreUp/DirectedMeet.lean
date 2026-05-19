import BEDC.Derived.DyadicRatCoreUp.DirectedRefinementRadiusHandoff

namespace BEDC.Derived.DyadicRatCoreUp

open BEDC.Derived.RatUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicRatCoreCarrier_finite_radius_window_directed_meet [AskSetup] [PackageSetup]
    {m0 e0 l0 p0 m1 e1 l1 p1 common leftScale rightScale scaledLeft scaledRight
      classifierWindow radiusWindow0 radiusWindow1 handoff0 handoff1 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicRatCoreCarrier m0 e0 l0 p0 ->
      DyadicRatCoreCarrier m1 e1 l1 p1 ->
        PositiveUnaryDenominator common ->
          Cont e0 common leftScale ->
            Cont e1 common rightScale ->
              Cont m0 leftScale scaledLeft ->
                Cont m1 rightScale scaledRight ->
                  RatHistoryClassifier scaledLeft scaledRight ->
                    Cont scaledLeft scaledRight classifierWindow ->
                      Cont classifierWindow common radiusWindow0 ->
                        Cont classifierWindow common radiusWindow1 ->
                          Cont radiusWindow0 p0 handoff0 ->
                            Cont radiusWindow1 p0 handoff1 ->
                              PkgSig bundle handoff0 pkg ->
                                PkgSig bundle handoff1 pkg ->
                                  hsame radiusWindow0 radiusWindow1 ∧
                                    UnaryHistory radiusWindow0 ∧
                                      UnaryHistory radiusWindow1 ∧
                                        UnaryHistory handoff0 ∧ UnaryHistory handoff1 ∧
                                          PkgSig bundle handoff0 pkg ∧
                                            PkgSig bundle handoff1 pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig RatHistoryClassifier
  intro carrier0 carrier1 commonPositive e0CommonLeftScale e1CommonRightScale
    m0LeftScaleScaledLeft m1RightScaleScaledRight classified scaledClassifierWindow
    classifierCommonRadius0 classifierCommonRadius1 radiusProvenanceHandoff0
    radiusProvenanceHandoff1 handoffPkg0 handoffPkg1
  have handoffSurface0 :=
    DyadicRatCoreCarrier_directed_refinement_radius_handoff
      (m0 := m0) (e0 := e0) (l0 := l0) (p0 := p0) (m1 := m1) (e1 := e1)
      (l1 := l1) (p1 := p1) (common := common) (leftScale := leftScale)
      (rightScale := rightScale) (scaledLeft := scaledLeft) (scaledRight := scaledRight)
      (classifierWindow := classifierWindow) (radiusWindow := radiusWindow0)
      (handoff := handoff0) (bundle := bundle) (pkg := pkg) carrier0 carrier1
      commonPositive e0CommonLeftScale e1CommonRightScale m0LeftScaleScaledLeft
      m1RightScaleScaledRight classified scaledClassifierWindow classifierCommonRadius0
      radiusProvenanceHandoff0 handoffPkg0
  have handoffSurface1 :=
    DyadicRatCoreCarrier_directed_refinement_radius_handoff
      (m0 := m0) (e0 := e0) (l0 := l0) (p0 := p0) (m1 := m1) (e1 := e1)
      (l1 := l1) (p1 := p1) (common := common) (leftScale := leftScale)
      (rightScale := rightScale) (scaledLeft := scaledLeft) (scaledRight := scaledRight)
      (classifierWindow := classifierWindow) (radiusWindow := radiusWindow1)
      (handoff := handoff1) (bundle := bundle) (pkg := pkg) carrier0 carrier1
      commonPositive e0CommonLeftScale e1CommonRightScale m0LeftScaleScaledLeft
      m1RightScaleScaledRight classified scaledClassifierWindow classifierCommonRadius1
      radiusProvenanceHandoff1 handoffPkg1
  have sameRadius : hsame radiusWindow0 radiusWindow1 :=
    cont_deterministic classifierCommonRadius0 classifierCommonRadius1
  exact
    ⟨sameRadius, handoffSurface0.right.right.left, handoffSurface1.right.right.left,
      handoffSurface0.right.right.right.left, handoffSurface1.right.right.right.left,
      handoffSurface0.right.right.right.right.right.right,
      handoffSurface1.right.right.right.right.right.right⟩

end BEDC.Derived.DyadicRatCoreUp
