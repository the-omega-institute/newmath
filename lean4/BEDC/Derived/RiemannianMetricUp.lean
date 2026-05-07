import BEDC.Derived.InnerProductUp
import BEDC.Derived.ManifoldUp
import BEDC.Derived.RealUp.Core
import BEDC.Derived.VecSpaceUp

namespace BEDC.Derived.RiemannianMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.InnerProductUp
open BEDC.Derived.ManifoldUp
open BEDC.Derived.RatUp
open BEDC.Derived.RealUp
open BEDC.Derived.VecSpaceUp

theorem RiemannianMetricSingleton_source_fibre_carrier_row {x u v metric : BHist} :
    ManifoldSingletonCarrier x ->
      VecSpaceSingletonCarrier u ->
        VecSpaceSingletonCarrier v ->
          hsame metric (InnerProductSingletonForm u v) ->
            ManifoldSingletonCarrier x ∧ VecSpaceSingletonCarrier u ∧
              VecSpaceSingletonCarrier v ∧
                RealConstantHistoryClassifier metric (BHist.e1 (BHist.e1 BHist.Empty)) ∧
                  UnaryHistory x ∧ UnaryHistory u ∧ UnaryHistory v := by
  intro pointCarrier sourceCarrier targetCarrier metricDisplayed
  have pointUnary : UnaryHistory x :=
    (ManifoldSingletonCarrier_topology_scope pointCarrier).right.left
  have sourceUnary : UnaryHistory u :=
    unary_transport unary_empty (hsame_symm sourceCarrier)
  have targetUnary : UnaryHistory v :=
    unary_transport unary_empty (hsame_symm targetCarrier)
  have ratClassifier :
      RatHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    RatHistoryClassifier_e1_tail_unary_iff.mpr
      (And.intro unary_empty (And.intro unary_empty (hsame_refl BHist.Empty)))
  have displayedClassifier :
      RealConstantHistoryClassifier (InnerProductSingletonForm u v)
        (BHist.e1 (BHist.e1 BHist.Empty)) := by
    unfold InnerProductSingletonForm
    exact RealConstantHistoryClassifier_e1_iff_rat.mpr ratClassifier
  have metricClassifier :
      RealConstantHistoryClassifier metric (BHist.e1 (BHist.e1 BHist.Empty)) :=
    RealConstantHistoryClassifier_endpoint_transport (hsame_symm metricDisplayed)
      (hsame_refl (BHist.e1 (BHist.e1 BHist.Empty))) displayedClassifier
  exact And.intro pointCarrier
    (And.intro sourceCarrier
      (And.intro targetCarrier
        (And.intro metricClassifier
          (And.intro pointUnary (And.intro sourceUnary targetUnary)))))

end BEDC.Derived.RiemannianMetricUp
