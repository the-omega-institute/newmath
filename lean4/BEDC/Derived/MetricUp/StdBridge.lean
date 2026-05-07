import BEDC.Derived.MetricUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem MetricUp_StdBridge {x y d : BHist} :
    UnaryHistory x ->
      UnaryHistory y ->
        MetricDistanceWitness x y d ->
          MetricDistanceWitness x y (append x y) ∧
            SemanticNameCert (MetricDistanceWitness x y) (MetricDistanceWitness x y)
              (MetricDistanceWitness x y) hsame ∧
                hsame d (append x y) := by
  intro xCarrier yCarrier witness
  exact And.intro
    (And.intro xCarrier
      (And.intro yCarrier
        (And.intro (unary_append_closed xCarrier yCarrier) (cont_intro rfl))))
    (And.intro (MetricDistanceWitness_semanticNameCert xCarrier yCarrier)
      (cont_deterministic witness.2.2.2 (cont_intro rfl)))

end BEDC.Derived.MetricUp
