import BEDC.Derived.MetricUp.RealDistancePublicLawPackage

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem MetricspaceRealalgorderPositiveRadiusBudgetInterface
    {x y dist radius witness budget classifier provenance realAlg budgetRead : BHist} :
    MetricspaceRealDistanceCarrier x y dist radius witness budget classifier provenance realAlg →
      Cont realAlg radius budgetRead →
        MetricDistanceWitness x y dist ∧ UnaryHistory radius ∧ UnaryHistory realAlg ∧
          UnaryHistory budgetRead ∧ Cont dist radius budget ∧
            Cont realAlg radius budgetRead ∧ hsame classifier dist := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame
  intro carrier realAlgRadiusBudget
  rcases carrier with
    ⟨distanceWitness, radiusUnary, distRadiusBudget, classifierSame, _witnessBudgetProvenance,
      realAlgUnary⟩
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed realAlgUnary radiusUnary realAlgRadiusBudget
  exact
    ⟨distanceWitness, radiusUnary, realAlgUnary, budgetReadUnary, distRadiusBudget,
      realAlgRadiusBudget, classifierSame⟩

end BEDC.Derived.MetricUp
