import BEDC.Derived.FieldUp.Affine

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

theorem field_affine_composite_inverse_reverse_coherence
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
    (pa' : NonZero a') (pb' : NonZero b') (pA : NonZero (mul a' a))
    (pB : NonZero (mul b b'))
    (compositeCollected : forall x : BHist,
      hsame
        (add (mul (mul (mul a' a) x) (mul b b')) (add (mul (mul a' d) b') d'))
        (add (mul (mul a' (add (mul (mul a x) b) d)) b') d')) :
    hsame
      (mul (inv (mul a' a) pA)
        (mul (add q (neg (add (mul (mul a' d) b') d'))) (inv (mul b b') pB)))
      (mul (inv a pa)
        (mul
          (add (mul (inv a' pa') (mul (add q (neg d')) (inv b' pb'))) (neg d))
          (inv b pb))) := by
  have collectedSolves :
      hsame
        (add
          (mul
            (mul (mul a' a)
              (mul (inv (mul a' a) pA)
                (mul (add q (neg (add (mul (mul a' d) b') d')))
                  (inv (mul b b') pB))))
            (mul b b'))
          (add (mul (mul a' d) b') d'))
        q := by
    have collectedCertificate :=
      field_affine_explicit_inverse_certified_automorphism addAssoc addRightId addCongr
        negLeft negRight mulAssoc mulLeftId mulRightId mulCongr mulLeftInv mulRightInv
        (a := mul a' a) (b := mul b b') (d := add (mul (mul a' d) b') d')
        (c := q) (e := q) (x := q) pA pB
    exact collectedCertificate.right.left
  have reverseSolvesComposite :
      hsame
        (add
          (mul
            (mul a'
              (add
                (mul
                  (mul a
                    (mul (inv a pa)
                      (mul
                        (add
                          (mul (inv a' pa') (mul (add q (neg d')) (inv b' pb')))
                          (neg d))
                        (inv b pb))))
                  b)
                d))
            b')
          d')
        q := by
    have compositeCertificate :=
      field_affine_composite_two_sided_inverse addAssoc addRightId addCongr
        negLeft negRight mulAssoc mulLeftId mulRightId mulCongr mulLeftInv mulRightInv
        (a := a) (b := b) (c := a') (e := b') (d := d) (f := d') (x := q) (y := q)
        (q := q) pa pb pa' pb'
    exact compositeCertificate.right.left
  have reverseSolvesCollected :
      hsame
        (add
          (mul
            (mul (mul a' a)
              (mul (inv a pa)
                (mul
                  (add
                    (mul (inv a' pa') (mul (add q (neg d')) (inv b' pb')))
                    (neg d))
                  (inv b pb))))
            (mul b b'))
          (add (mul (mul a' d) b') d'))
        q := by
    exact hsame_trans
      (compositeCollected
        (mul (inv a pa)
          (mul
            (add (mul (inv a' pa') (mul (add q (neg d')) (inv b' pb'))) (neg d))
            (inv b pb))))
      reverseSolvesComposite
  exact
    field_affine_certified_fiber_singleton addAssoc addRightId addCongr negRight
      mulAssoc mulLeftId mulRightId mulCongr mulLeftInv mulRightInv
      (a := mul a' a) (b := mul b b') (d := add (mul (mul a' d) b') d') (c := q)
      (x := mul (inv (mul a' a) pA)
        (mul (add q (neg (add (mul (mul a' d) b') d'))) (inv (mul b b') pB)))
      (y := mul (inv a pa)
        (mul
          (add (mul (inv a' pa') (mul (add q (neg d')) (inv b' pb'))) (neg d))
          (inv b pb)))
      pA pB collectedSolves reverseSolvesCollected

end BEDC.Derived.FieldUp
