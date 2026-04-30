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

end BEDC.Derived.AbGroupUp
