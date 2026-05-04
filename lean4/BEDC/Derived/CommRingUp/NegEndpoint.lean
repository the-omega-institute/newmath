import BEDC.Derived.CommRingUp

namespace BEDC.Derived.CommRingUp

open BEDC.FKernel.Hist

theorem CommRingSingletonClassifier_neg_empty_endpoint_iff {h t : BHist} :
    CommRingSingletonCarrier h ->
      (CommRingSingletonClassifier (CommRingSingletonNeg h) t ↔
        CommRingSingletonCarrier t ∧ hsame (CommRingSingletonNeg h) BHist.Empty) := by
  intro _carrierH
  constructor
  · intro classified
    exact And.intro classified.right.left classified.left
  · intro endpoint
    have leftCarrier : CommRingSingletonCarrier (CommRingSingletonNeg h) := endpoint.right
    exact And.intro leftCarrier
      (And.intro endpoint.left (hsame_trans leftCarrier (hsame_symm endpoint.left)))

end BEDC.Derived.CommRingUp
