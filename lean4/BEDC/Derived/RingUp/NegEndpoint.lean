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

theorem RingSingletonClassifier_mul_empty_endpoint_iff {h k out : BHist} :
    RingSingletonClassifier (RingSingletonMul h k) out ↔ hsame out BHist.Empty := by
  constructor
  · intro classified
    exact classified.right.left
  · intro outEmpty
    have leftCarrier : RingSingletonCarrier (RingSingletonMul h k) :=
      hsame_refl BHist.Empty
    exact And.intro leftCarrier (And.intro outEmpty (hsame_symm outEmpty))

end BEDC.Derived.RingUp
