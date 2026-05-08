import BEDC.Derived.HilbertUp
import BEDC.Derived.LieGroupUp
import BEDC.FKernel.Cont.Units

namespace BEDC.Derived.UnitaryGroupUp

open BEDC.Derived.HilbertUp
open BEDC.Derived.LieGroupUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem UnitaryGroupCarrierClassifier_obligation {hilbert automorphism endpoint : BHist} :
    VecSpaceSingletonCarrier hilbert -> LieGroupSingletonCarrier automorphism ->
      Cont hilbert automorphism endpoint ->
        VecSpaceSingletonCarrier hilbert ∧ LieGroupSingletonCarrier automorphism ∧
          Cont hilbert automorphism endpoint ∧ hsame endpoint hilbert := by
  intro hilbertCarrier automorphismCarrier endpointRow
  have endpointReadback : hsame endpoint hilbert := by
    cases automorphismCarrier
    exact cont_right_unit_result endpointRow
  exact And.intro hilbertCarrier
    (And.intro automorphismCarrier (And.intro endpointRow endpointReadback))

end BEDC.Derived.UnitaryGroupUp
