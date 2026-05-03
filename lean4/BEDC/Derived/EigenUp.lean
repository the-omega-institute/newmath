import BEDC.Derived.LinearMapUp
import BEDC.Derived.DeterminantUp

namespace BEDC.Derived.EigenUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.LinearMapUp
open BEDC.Derived.DeterminantUp

def EigenSingletonCarrier (pair : BHist) : Prop :=
  ∃ map scalar vector : BHist,
    LinearMapSingletonCarrier map ∧
      DeterminantSingletonCarrier scalar ∧
        LinearMapSingletonCarrier vector ∧ Cont map (append scalar vector) pair

theorem EigenSingletonCarrier_cont_result_transport {map scalar vector pair pair' : BHist} :
    LinearMapSingletonCarrier map ->
      DeterminantSingletonCarrier scalar ->
        LinearMapSingletonCarrier vector ->
          Cont map (append scalar vector) pair -> hsame pair pair' ->
            EigenSingletonCarrier pair' := by
  intro mapCarrier scalarCarrier vectorCarrier contPair samePair
  exact Exists.intro map
    (Exists.intro scalar
      (Exists.intro vector
        (And.intro mapCarrier
          (And.intro scalarCarrier
            (And.intro vectorCarrier (cont_result_hsame_transport contPair samePair))))))

end BEDC.Derived.EigenUp
