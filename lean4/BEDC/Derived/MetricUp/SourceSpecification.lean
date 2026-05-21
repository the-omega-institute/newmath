import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def MetricSourceSpecification (x y d provenance name : BHist) : Prop :=
  MetricDistanceWitness x y d ∧ Cont d provenance name ∧ UnaryHistory name

theorem MetricSourceSpecification_rows {x y d provenance name : BHist} :
    MetricSourceSpecification x y d provenance name →
      MetricDistanceWitness x y d ∧ Cont d provenance name ∧ UnaryHistory name := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory MetricDistanceWitness
  intro source
  exact source

end BEDC.Derived.MetricUp
