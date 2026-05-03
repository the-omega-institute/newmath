import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

theorem field_affine_empty_offset_composition_normal_form
    {add mul : BHist -> BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulAssoc : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    {a b c e d x : BHist} :
    hsame (add (mul (mul c (add (mul (mul a x) b) d)) e) BHist.Empty)
      (add (mul (mul (mul c a) x) (mul b e)) (add (mul (mul c d) e) BHist.Empty)) := by
  have leftExpanded :
      hsame (mul (mul c (add (mul (mul a x) b) d)) e)
        (mul (add (mul c (mul (mul a x) b)) (mul c d)) e) := by
    exact mulCongr (leftDistrib c (mul (mul a x) b) d) (hsame_refl e)
  have distributed :
      hsame (mul (add (mul c (mul (mul a x) b)) (mul c d)) e)
        (add (mul (mul c (mul (mul a x) b)) e) (mul (mul c d) e)) := by
    exact rightDistrib (mul c (mul (mul a x) b)) (mul c d) e
  have productNormal :
      hsame (mul (mul c (mul (mul a x) b)) e)
        (mul (mul (mul c a) x) (mul b e)) := by
    have reassocOuter :
        hsame (mul (mul c (mul (mul a x) b)) e)
          (mul c (mul (mul (mul a x) b) e)) := by
      exact mulAssoc c (mul (mul a x) b) e
    have reassocTail :
        hsame (mul c (mul (mul (mul a x) b) e))
          (mul c (mul (mul a x) (mul b e))) := by
      exact mulCongr (hsame_refl c) (mulAssoc (mul a x) b e)
    have reassocHead :
        hsame (mul c (mul (mul a x) (mul b e)))
          (mul (mul c (mul a x)) (mul b e)) := by
      exact hsame_symm (mulAssoc c (mul a x) (mul b e))
    have collectHead :
        hsame (mul (mul c (mul a x)) (mul b e))
          (mul (mul (mul c a) x) (mul b e)) := by
      exact mulCongr (hsame_symm (mulAssoc c a x)) (hsame_refl (mul b e))
    exact hsame_trans reassocOuter
      (hsame_trans reassocTail (hsame_trans reassocHead collectHead))
  have expandedNormal :
      hsame (add (mul (mul c (mul (mul a x) b)) e) (mul (mul c d) e))
        (add (mul (mul (mul c a) x) (mul b e)) (mul (mul c d) e)) := by
    exact addCongr productNormal (hsame_refl (mul (mul c d) e))
  have withOffset :
      hsame (add (add (mul (mul c (mul (mul a x) b)) e) (mul (mul c d) e))
          BHist.Empty)
        (add (add (mul (mul (mul c a) x) (mul b e)) (mul (mul c d) e))
          BHist.Empty) := by
    exact addCongr expandedNormal (hsame_refl BHist.Empty)
  have reassocAdd :
      hsame (add (add (mul (mul (mul c a) x) (mul b e)) (mul (mul c d) e))
          BHist.Empty)
        (add (mul (mul (mul c a) x) (mul b e)) (add (mul (mul c d) e) BHist.Empty)) := by
    exact addAssoc (mul (mul (mul c a) x) (mul b e)) (mul (mul c d) e) BHist.Empty
  exact hsame_trans (addCongr (hsame_trans leftExpanded distributed) (hsame_refl BHist.Empty))
    (hsame_trans withOffset reassocAdd)

theorem field_affine_inverse_offset_empty_normal_form
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (mulAssoc : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    {a b d c : BHist} (pa : NonZero a) (pb : NonZero b) :
    hsame (add (mul (inv a pa) (mul (add c (neg d)) (inv b pb))) BHist.Empty)
      (add (add (mul (mul (inv a pa) c) (inv b pb))
        (mul (mul (inv a pa) (neg d)) (inv b pb))) BHist.Empty) := by
  have reassoc :
      hsame (mul (inv a pa) (mul (add c (neg d)) (inv b pb)))
        (mul (mul (inv a pa) (add c (neg d))) (inv b pb)) := by
    exact hsame_symm (mulAssoc (inv a pa) (add c (neg d)) (inv b pb))
  have splitLeft :
      hsame (mul (mul (inv a pa) (add c (neg d))) (inv b pb))
        (mul (add (mul (inv a pa) c) (mul (inv a pa) (neg d))) (inv b pb)) := by
    exact mulCongr (leftDistrib (inv a pa) c (neg d)) (hsame_refl (inv b pb))
  have splitRight :
      hsame (mul (add (mul (inv a pa) c) (mul (inv a pa) (neg d))) (inv b pb))
        (add (mul (mul (inv a pa) c) (inv b pb))
          (mul (mul (inv a pa) (neg d)) (inv b pb))) := by
    exact rightDistrib (mul (inv a pa) c) (mul (inv a pa) (neg d)) (inv b pb)
  exact addCongr (hsame_trans reassoc (hsame_trans splitLeft splitRight))
    (hsame_refl BHist.Empty)

theorem field_affine_composition_right_empty_normal_form
    {add mul : BHist -> BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulAssoc : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    {a b c e d f x : BHist} :
    hsame (add (add (mul (mul c (add (mul (mul a x) b) d)) e) f) BHist.Empty)
      (add (add (mul (mul (mul c a) x) (mul b e))
        (add (mul (mul c d) e) f)) BHist.Empty) := by
  have leftExpanded :
      hsame (mul (mul c (add (mul (mul a x) b) d)) e)
        (mul (add (mul c (mul (mul a x) b)) (mul c d)) e) := by
    exact mulCongr (leftDistrib c (mul (mul a x) b) d) (hsame_refl e)
  have distributed :
      hsame (mul (add (mul c (mul (mul a x) b)) (mul c d)) e)
        (add (mul (mul c (mul (mul a x) b)) e) (mul (mul c d) e)) := by
    exact rightDistrib (mul c (mul (mul a x) b)) (mul c d) e
  have productNormal :
      hsame (mul (mul c (mul (mul a x) b)) e)
        (mul (mul (mul c a) x) (mul b e)) := by
    have reassocOuter :
        hsame (mul (mul c (mul (mul a x) b)) e)
          (mul c (mul (mul (mul a x) b) e)) := by
      exact mulAssoc c (mul (mul a x) b) e
    have reassocTail :
        hsame (mul c (mul (mul (mul a x) b) e))
          (mul c (mul (mul a x) (mul b e))) := by
      exact mulCongr (hsame_refl c) (mulAssoc (mul a x) b e)
    have reassocHead :
        hsame (mul c (mul (mul a x) (mul b e)))
          (mul (mul c (mul a x)) (mul b e)) := by
      exact hsame_symm (mulAssoc c (mul a x) (mul b e))
    have collectHead :
        hsame (mul (mul c (mul a x)) (mul b e))
          (mul (mul (mul c a) x) (mul b e)) := by
      exact mulCongr (hsame_symm (mulAssoc c a x)) (hsame_refl (mul b e))
    exact hsame_trans reassocOuter
      (hsame_trans reassocTail (hsame_trans reassocHead collectHead))
  have productSplit :
      hsame (mul (mul c (add (mul (mul a x) b) d)) e)
        (add (mul (mul (mul c a) x) (mul b e)) (mul (mul c d) e)) := by
    exact hsame_trans leftExpanded
      (hsame_trans distributed (addCongr productNormal (hsame_refl (mul (mul c d) e))))
  have withOffset :
      hsame (add (add (mul (mul c (add (mul (mul a x) b) d)) e) f) BHist.Empty)
        (add (add (add (mul (mul (mul c a) x) (mul b e)) (mul (mul c d) e)) f)
          BHist.Empty) := by
    exact addCongr (addCongr productSplit (hsame_refl f)) (hsame_refl BHist.Empty)
  have reassocOffset :
      hsame (add (add (add (mul (mul (mul c a) x) (mul b e)) (mul (mul c d) e)) f)
          BHist.Empty)
        (add (add (mul (mul (mul c a) x) (mul b e)) (add (mul (mul c d) e) f))
          BHist.Empty) := by
    exact addCongr
      (addAssoc (mul (mul (mul c a) x) (mul b e)) (mul (mul c d) e) f)
      (hsame_refl BHist.Empty)
  exact hsame_trans withOffset reassocOffset

end BEDC.Derived.FieldUp
