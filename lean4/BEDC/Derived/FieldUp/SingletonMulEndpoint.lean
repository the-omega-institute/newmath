import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

theorem FieldSingletonClassifier_mul_empty_endpoint_iff {h k out : BHist} :
    FieldSingletonClassifier (FieldSingletonMul h k) out ↔ hsame out BHist.Empty := by
  constructor
  · intro classified
    exact classified.right.left
  · intro outEmpty
    have leftCarrier : FieldSingletonCarrier (FieldSingletonMul h k) :=
      hsame_refl BHist.Empty
    exact And.intro leftCarrier (And.intro outEmpty (hsame_symm outEmpty))

theorem FieldSingletonAdd_endpoint_classifier_iff {h k out : BHist} :
    FieldSingletonClassifier (FieldSingletonAdd h k) out ↔ hsame out BHist.Empty := by
  constructor
  · intro classified
    exact classified.right.left
  · intro outEmpty
    exact And.intro (hsame_refl BHist.Empty)
      (And.intro outEmpty (hsame_symm outEmpty))

theorem FieldSingletonNeg_endpoint_classifier_iff {h out : BHist} :
    FieldSingletonClassifier (FieldSingletonNeg h) out <-> hsame out BHist.Empty := by
  constructor
  · intro classified
    exact classified.right.left
  · intro outEmpty
    have leftCarrier : FieldSingletonCarrier (FieldSingletonNeg h) := hsame_refl BHist.Empty
    exact And.intro leftCarrier
      (And.intro outEmpty (hsame_trans leftCarrier (hsame_symm outEmpty)))

end BEDC.Derived.FieldUp
