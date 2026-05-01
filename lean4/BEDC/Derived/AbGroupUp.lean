import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.Derived.GroupUp

namespace BEDC.Derived.AbGroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem abgroup_mul_left_right_swap {mul : BHist -> BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (commC : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b')) :
    forall a b c : BHist, hsame (mul a (mul b c)) (mul b (mul a c)) := by
  intro a b c
  exact hsame_trans (hsame_symm (assocC a b c))
    (hsame_trans (mulCongr (commC a b) (hsame_refl c)) (assocC b a c))

theorem abgroup_mul_middle_four {mul : BHist -> BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (commC : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b')) :
    forall a b c d : BHist,
      hsame (mul (mul a b) (mul c d)) (mul (mul a c) (mul b d)) := by
  intro a b c d
  have reassocLeft :
      hsame (mul (mul a b) (mul c d)) (mul a (mul b (mul c d))) := by
    exact assocC a b (mul c d)
  have swapRight : hsame (mul b (mul c d)) (mul c (mul b d)) := by
    exact abgroup_mul_left_right_swap assocC commC mulCongr b c d
  have transportRight :
      hsame (mul a (mul b (mul c d))) (mul a (mul c (mul b d))) := by
    exact mulCongr (hsame_refl a) swapRight
  have reassocRight :
      hsame (mul a (mul c (mul b d))) (mul (mul a c) (mul b d)) := by
    exact hsame_symm (assocC a c (mul b d))
  exact hsame_trans reassocLeft (hsame_trans transportRight reassocRight)

theorem abgroup_conjugation_collapse {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (commC : forall x y : BHist, hsame (mul x y) (mul y x))
    (rightId : forall x : BHist, hsame (mul x e) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (rightInv : forall x : BHist, hsame (mul x (inv x)) e) :
    forall a b : BHist, hsame (mul a (mul b (inv a))) b := by
  intro a b
  have swap :
      hsame (mul a (mul b (inv a))) (mul b (mul a (inv a))) := by
    exact abgroup_mul_left_right_swap assocC commC mulCongr a b (inv a)
  have collapseInner : hsame (mul b (mul a (inv a))) (mul b e) := by
    exact mulCongr (hsame_refl b) (rightInv a)
  exact hsame_trans swap (hsame_trans collapseInner (rightId b))

theorem abgroup_inverse_conjugation_collapse {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (commC : forall x y : BHist, hsame (mul x y) (mul y x))
    (rightId : forall x : BHist, hsame (mul x e) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) e) :
    forall a b : BHist, hsame (mul (inv a) (mul b a)) b := by
  intro a b
  have swap :
      hsame (mul (inv a) (mul b a)) (mul b (mul (inv a) a)) := by
    exact abgroup_mul_left_right_swap assocC commC mulCongr (inv a) b a
  have collapseInner : hsame (mul b (mul (inv a) a)) (mul b e) := by
    exact mulCongr (hsame_refl b) (leftInv a)
  exact hsame_trans swap (hsame_trans collapseInner (rightId b))

theorem abgroup_inverse_mul {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul e x) x)
    (rightId : forall x : BHist, hsame (mul x e) x)
    (commC : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) e)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) e) :
    forall x y : BHist, hsame (inv (mul x y)) (mul (inv x) (inv y)) := by
  intro x y
  exact hsame_trans
    (BEDC.Derived.GroupUp.group_inverse_mul_reverse assocC leftId rightId mulCongr
      leftInv rightInv x y)
    (commC (inv y) (inv x))

theorem abgroup_mul_right_factor_swap {mul : BHist -> BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (commC : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b')) :
    forall a b c : BHist, hsame (mul (mul a b) c) (mul (mul a c) b) := by
  intro a b c
  exact hsame_trans (assocC a b c)
    (hsame_trans (mulCongr (hsame_refl a) (commC b c)) (hsame_symm (assocC a c b)))

theorem abgroup_mul_common_left_factor_collect {mul : BHist -> BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (commC : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b')) :
    forall a b c : BHist, hsame (mul (mul a b) (mul a c)) (mul a (mul a (mul b c))) := by
  intro a b c
  have reassoc :
      hsame (mul (mul a b) (mul a c)) (mul a (mul b (mul a c))) := by
    exact assocC a b (mul a c)
  have collectTail : hsame (mul b (mul a c)) (mul a (mul b c)) := by
    exact abgroup_mul_left_right_swap assocC commC mulCongr b a c
  have transportTail :
      hsame (mul a (mul b (mul a c))) (mul a (mul a (mul b c))) := by
    exact mulCongr (hsame_refl a) collectTail
  exact hsame_trans reassoc transportTail

theorem abgroup_mul_common_right_factor_collect {mul : BHist -> BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (commC : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b')) :
    forall a b c : BHist, hsame (mul (mul b a) (mul c a))
      (mul a (mul a (mul b c))) := by
  intro a b c
  have exposeLeftFactors :
      hsame (mul (mul b a) (mul c a)) (mul (mul a b) (mul a c)) := by
    exact mulCongr (commC b a) (commC c a)
  have collect :
      hsame (mul (mul a b) (mul a c)) (mul a (mul a (mul b c))) := by
    exact abgroup_mul_common_left_factor_collect assocC commC mulCongr a b c
  exact hsame_trans exposeLeftFactors collect

theorem abgroup_mul_balanced_cancel {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (commC : forall x y : BHist, hsame (mul x y) (mul y x))
    (leftId : forall x, hsame (mul e x) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x, hsame (mul (inv x) x) e) {a b c : BHist} :
    hsame (mul a b) (mul c a) -> hsame b c := by
  intro sameBalanced
  exact BEDC.Derived.GroupUp.group_left_cancel assocC leftId mulCongr leftInv
    (hsame_trans sameBalanced (commC c a))

theorem history_append_nonempty_left_ne_right :
    (forall {h k : BHist}, append (BHist.e0 h) k = k -> False) ∧
      (forall {h k : BHist}, append (BHist.e1 h) k = k -> False) := by
  constructor
  · intro h k same
    induction k generalizing h with
    | Empty =>
        cases same
    | e0 k ih =>
        exact ih (BHist.e0.inj same)
    | e1 k ih =>
        exact ih (BHist.e1.inj same)
  · intro h k same
    induction k generalizing h with
    | Empty =>
        cases same
    | e0 k ih =>
        exact ih (BHist.e0.inj same)
    | e1 k ih =>
        exact ih (BHist.e1.inj same)

end BEDC.Derived.AbGroupUp
