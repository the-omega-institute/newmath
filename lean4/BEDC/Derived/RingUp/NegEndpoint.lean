import BEDC.Derived.RingUp

namespace BEDC.Derived.RingUp

open BEDC.FKernel.Hist

theorem RingSingletonClassifier_neg_empty_endpoint_iff {h t : BHist} :
    RingSingletonCarrier h ->
      (RingSingletonClassifier (RingSingletonNeg h) t ↔
        RingSingletonCarrier t ∧ hsame (RingSingletonNeg h) BHist.Empty) := by
  intro _carrierH
  constructor
  · intro classified
    exact And.intro classified.right.left classified.left
  · intro endpoint
    have leftCarrier : RingSingletonCarrier (RingSingletonNeg h) := endpoint.right
    exact And.intro leftCarrier
      (And.intro endpoint.left (hsame_trans leftCarrier (hsame_symm endpoint.left)))

end BEDC.Derived.RingUp
