import BEDC.Derived.FieldUp.ProductWitnessIndependence
import BEDC.Derived.FieldUp.AffineCompositeInverseReverseCoherence

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

theorem field_affine_composite_inverse_product_witness_independence
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addRightId : forall x : BHist, hsame (add x BHist.Empty) x)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (negRight : forall x : BHist, hsame (add x (neg x)) BHist.Empty)
    (mulAssoc : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (mulLeftId : forall x : BHist, hsame (mul one x) x)
    (mulRightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (mulLeftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (mulRightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b a' b' d d' q : BHist} (pa : NonZero a) (pb : NonZero b)
    (pa' : NonZero a') (pb' : NonZero b') (pA pA' : NonZero (mul a' a))
    (pB pB' : NonZero (mul b b'))
    (compositeCollected : forall x : BHist,
      hsame
        (add (mul (mul (mul a' a) x) (mul b b')) (add (mul (mul a' d) b') d'))
        (add (mul (mul a' (add (mul (mul a x) b) d)) b') d')) :
    let collected := fun pA pB q =>
      mul (inv (mul a' a) pA)
        (mul (add q (neg (add (mul (mul a' d) b') d'))) (inv (mul b b') pB))
    let reverse := fun q =>
      mul (inv a pa)
        (mul
          (add (mul (inv a' pa') (mul (add q (neg d')) (inv b' pb'))) (neg d))
          (inv b pb))
    hsame (collected pA pB q) (collected pA' pB' q) ∧
      hsame (collected pA pB q) (reverse q) ∧
        hsame (collected pA' pB' q) (reverse q) := by
  have collectedIndependence :=
    field_affine_product_witness_independence
      (add := add) (mul := mul) (neg := neg) (one := one) (NonZero := NonZero)
      (inv := inv) addRightId negRight mulAssoc mulLeftId mulRightId mulCongr
      mulLeftInv mulRightInv
      (A := mul a' a) (B := mul b b') (D := add (mul (mul a' d) b') d')
      (x := q) (q := q) pA pA' pB pB'
  have firstRow :
      hsame
        (mul (inv (mul a' a) pA)
          (mul (add q (neg (add (mul (mul a' d) b') d'))) (inv (mul b b') pB)))
        (mul (inv (mul a' a) pA')
          (mul (add q (neg (add (mul (mul a' d) b') d'))) (inv (mul b b') pB'))) := by
    exact collectedIndependence.right
  have secondRow :=
    field_affine_composite_inverse_reverse_coherence
      (add := add) (mul := mul) (neg := neg) (one := one) (NonZero := NonZero)
      (inv := inv) addAssoc addRightId addCongr negLeft negRight mulAssoc mulLeftId
      mulRightId mulCongr mulLeftInv mulRightInv
      (a := a) (b := b) (a' := a') (b' := b') (d := d) (d' := d') (q := q)
      pa pb pa' pb' pA pB compositeCollected
  have thirdRow :=
    field_affine_composite_inverse_reverse_coherence
      (add := add) (mul := mul) (neg := neg) (one := one) (NonZero := NonZero)
      (inv := inv) addAssoc addRightId addCongr negLeft negRight mulAssoc mulLeftId
      mulRightId mulCongr mulLeftInv mulRightInv
      (a := a) (b := b) (a' := a') (b' := b') (d := d) (d' := d') (q := q)
      pa pb pa' pb' pA' pB' compositeCollected
  exact And.intro firstRow (And.intro secondRow thirdRow)

end BEDC.Derived.FieldUp
