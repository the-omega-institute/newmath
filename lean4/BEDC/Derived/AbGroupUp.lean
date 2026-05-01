import BEDC.FKernel.Hist
import BEDC.Derived.GroupUp

namespace BEDC.Derived.AbGroupUp

open BEDC.FKernel.Hist

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

end BEDC.Derived.AbGroupUp
