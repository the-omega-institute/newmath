import BEDC.Derived.AdjunctionUp

namespace BEDC.Derived.AdjunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def AdjunctionUnitCounitCarrierSwap
    (p q a unit counit left right p' q' a' unit' counit' left' right' : BHist) :
    Prop :=
  hsame p' q ∧ hsame q' p ∧ hsame a' a ∧ hsame unit' counit ∧
    hsame counit' unit ∧ hsame left' right ∧ hsame right' left

def AdjunctionUnitCounitDisplaySame
    (p q a unit counit left right p' q' a' unit' counit' left' right' : BHist) :
    Prop :=
  hsame p p' ∧ hsame q q' ∧ hsame a a' ∧ hsame unit unit' ∧
    hsame counit counit' ∧ hsame left left' ∧ hsame right right'

theorem AdjunctionUnitCounitCarrier_swap_involution
    {p0 q0 a0 u0 c0 l0 r0 p1 q1 a1 u1 c1 l1 r1 p2 q2 a2 u2 c2 l2 r2 :
      BHist} :
    AdjunctionUnitCounitCarrier p0 q0 a0 u0 c0 l0 r0 ->
      AdjunctionUnitCounitCarrierSwap p0 q0 a0 u0 c0 l0 r0 p1 q1 a1 u1 c1 l1 r1 ->
        AdjunctionUnitCounitCarrierSwap p1 q1 a1 u1 c1 l1 r1 p2 q2 a2 u2 c2 l2 r2 ->
          AdjunctionUnitCounitCarrier p2 q2 a2 u2 c2 l2 r2 ∧
            AdjunctionUnitCounitDisplaySame p0 q0 a0 u0 c0 l0 r0
              p2 q2 a2 u2 c2 l2 r2 ∧
              Cont u2 c2 l2 ∧ Cont c2 u2 r2 := by
  intro carrier firstSwap secondSwap
  cases firstSwap.left
  cases firstSwap.right.left
  cases firstSwap.right.right.left
  cases firstSwap.right.right.right.left
  cases firstSwap.right.right.right.right.left
  cases firstSwap.right.right.right.right.right.left
  cases firstSwap.right.right.right.right.right.right
  cases secondSwap.left
  cases secondSwap.right.left
  cases secondSwap.right.right.left
  cases secondSwap.right.right.right.left
  cases secondSwap.right.right.right.right.left
  cases secondSwap.right.right.right.right.right.left
  cases secondSwap.right.right.right.right.right.right
  exact
    And.intro carrier
      (And.intro
        (And.intro (hsame_refl p0)
          (And.intro (hsame_refl q0)
            (And.intro (hsame_refl a0)
              (And.intro (hsame_refl u0)
                (And.intro (hsame_refl c0)
                  (And.intro (hsame_refl l0) (hsame_refl r0)))))))
        (And.intro carrier.right.right.left carrier.right.right.right))

theorem AdjunctionTriangleCarrier_swap_involution
    {p0 q0 a0 u0 c0 l0 r0 p1 q1 a1 u1 c1 l1 r1 p2 q2 a2 u2 c2 l2 r2 :
      BHist} :
    AdjunctionTriangleCarrier p0 q0 a0 u0 c0 l0 r0 ->
      AdjunctionUnitCounitCarrierSwap p0 q0 a0 u0 c0 l0 r0 p1 q1 a1 u1 c1 l1 r1 ->
        AdjunctionUnitCounitCarrierSwap p1 q1 a1 u1 c1 l1 r1 p2 q2 a2 u2 c2 l2 r2 ->
          AdjunctionTriangleCarrier p2 q2 a2 u2 c2 l2 r2 ∧
            AdjunctionUnitCounitDisplaySame p0 q0 a0 u0 c0 l0 r0
              p2 q2 a2 u2 c2 l2 r2 ∧
              Cont u2 c2 l2 ∧ Cont c2 u2 r2 := by
  intro carrier firstSwap secondSwap
  cases firstSwap.left
  cases firstSwap.right.left
  cases firstSwap.right.right.left
  cases firstSwap.right.right.right.left
  cases firstSwap.right.right.right.right.left
  cases firstSwap.right.right.right.right.right.left
  cases firstSwap.right.right.right.right.right.right
  cases secondSwap.left
  cases secondSwap.right.left
  cases secondSwap.right.right.left
  cases secondSwap.right.right.right.left
  cases secondSwap.right.right.right.right.left
  cases secondSwap.right.right.right.right.right.left
  cases secondSwap.right.right.right.right.right.right
  exact
    And.intro carrier
      (And.intro
        (And.intro (hsame_refl p0)
          (And.intro (hsame_refl q0)
            (And.intro (hsame_refl a0)
              (And.intro (hsame_refl u0)
                (And.intro (hsame_refl c0)
                  (And.intro (hsame_refl l0) (hsame_refl r0)))))))
        (And.intro carrier.right.right.left carrier.right.right.right))

end BEDC.Derived.AdjunctionUp
