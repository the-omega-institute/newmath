import BEDC.Derived.AdjunctionUp

namespace BEDC.Derived.AdjunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem AdjunctionTriangleCarrier_carrier_swap_iff
    {left right object unit counit leftLeg rightLeg : BHist} :
    AdjunctionTriangleCarrier left right object unit counit leftLeg rightLeg ↔
      AdjunctionTriangleCarrier right left object counit unit rightLeg leftLeg := by
  constructor
  · intro h
    have leftRel : Cont unit counit leftLeg := h.right.right.left
    have rightRel : Cont counit unit rightLeg := h.right.right.right
    exact And.intro h.right.left (And.intro h.left (And.intro rightRel leftRel))
  · intro h
    have rightRel : Cont counit unit rightLeg := h.right.right.left
    have leftRel : Cont unit counit leftLeg := h.right.right.right
    exact And.intro h.right.left (And.intro h.left (And.intro leftRel rightRel))

theorem AdjunctionUnitCounitCarrier_carrier_swap_iff {p q a unit counit left right : BHist} :
    AdjunctionUnitCounitCarrier p q a unit counit left right ↔
      AdjunctionUnitCounitCarrier q p a counit unit right left := by
  constructor
  · intro h
    have leftRel : Cont unit counit left := h.right.right.left
    have rightRel : Cont counit unit right := h.right.right.right
    exact And.intro h.right.left (And.intro h.left (And.intro rightRel leftRel))
  · intro h
    have rightRel : Cont counit unit right := h.right.right.left
    have leftRel : Cont unit counit left := h.right.right.right
    exact And.intro h.right.left (And.intro h.left (And.intro leftRel rightRel))

end BEDC.Derived.AdjunctionUp
