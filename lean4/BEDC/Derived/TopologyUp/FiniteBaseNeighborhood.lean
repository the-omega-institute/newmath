import BEDC.Derived.TopologyUp.Core

namespace BEDC.Derived.TopologyUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist

theorem BHistFiniteBaseNeighborhood_append_decomposition
    (left right : ProbeBundle BHist) (ball : BHist -> BHist -> Prop) (x : BHist) :
    BHistFiniteBaseNeighborhood (bundleAppend left right) ball x <->
      BHistFiniteBaseNeighborhood left ball x ∧ BHistFiniteBaseNeighborhood right ball x := by
  constructor
  · intro appended
    constructor
    · intro i inLeft
      have inAppended : InBundle i (bundleAppend left right) :=
        Iff.mpr inBundle_bundleAppend_iff (Or.inl inLeft)
      exact appended i inAppended
    · intro i inRight
      have inAppended : InBundle i (bundleAppend left right) :=
        Iff.mpr inBundle_bundleAppend_iff (Or.inr inRight)
      exact appended i inAppended
  · intro split i inAppended
    have inEither : InBundle i left ∨ InBundle i right :=
      Iff.mp inBundle_bundleAppend_iff inAppended
    cases inEither with
    | inl inLeft =>
        exact split.left i inLeft
    | inr inRight =>
        exact split.right i inRight

end BEDC.Derived.TopologyUp
