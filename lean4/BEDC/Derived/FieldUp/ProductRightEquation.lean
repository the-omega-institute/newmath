import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

 theorem field_product_right_mul_empty_equation_exact_from_apartness
    {mul : BHist -> BHist -> BHist} {one : BHist} {NonZero : BHist -> Prop}
    {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b x : BHist} (pab : NonZero (mul a b)) (pa : NonZero a) (pb : NonZero b) :
    hsame (mul x (mul a b)) BHist.Empty ↔
      hsame x (mul BHist.Empty (mul (inv b pb) (inv a pa))) := by
  have oneFactor :
      hsame (mul x (mul a b)) BHist.Empty ↔
        hsame x (mul BHist.Empty (inv (mul a b) pab)) := by
    exact field_right_mul_equation_exact_from_apartness
      assocC rightId mulCongr leftInv rightInv pab
  have reverseInverse :
      hsame (inv (mul a b) pab) (mul (inv b pb) (inv a pa)) := by
    exact field_inverse_product_reverse_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv pab pa pb
  constructor
  · intro productEmpty
    exact hsame_trans (Iff.mp oneFactor productEmpty)
      (mulCongr (hsame_refl BHist.Empty) reverseInverse)
  · intro reversedSolution
    have productInverseSolution :
        hsame x (mul BHist.Empty (inv (mul a b) pab)) := by
      exact hsame_trans reversedSolution
        (mulCongr (hsame_refl BHist.Empty) (hsame_symm reverseInverse))
    exact Iff.mpr oneFactor productInverseSolution

 theorem field_product_left_mul_empty_equation_exact_from_apartness
    {mul : BHist -> BHist -> BHist} {one : BHist} {NonZero : BHist -> Prop}
    {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b x : BHist} (pab : NonZero (mul a b)) (pa : NonZero a) (pb : NonZero b) :
    hsame (mul (mul a b) x) BHist.Empty <->
      hsame x (mul (mul (inv b pb) (inv a pa)) BHist.Empty) := by
  have oneFactor :
      hsame (mul (mul a b) x) BHist.Empty <->
        hsame x (mul (inv (mul a b) pab) BHist.Empty) := by
    exact field_left_mul_equation_exact_from_apartness
      assocC leftId mulCongr leftInv rightInv pab
  have reverseInverse :
      hsame (inv (mul a b) pab) (mul (inv b pb) (inv a pa)) := by
    exact field_inverse_product_reverse_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv pab pa pb
  constructor
  · intro productEmpty
    exact hsame_trans (Iff.mp oneFactor productEmpty)
      (mulCongr reverseInverse (hsame_refl BHist.Empty))
  · intro reversedSolution
    have productInverseSolution :
        hsame x (mul (inv (mul a b) pab) BHist.Empty) := by
      exact hsame_trans reversedSolution
        (mulCongr (hsame_symm reverseInverse) (hsame_refl BHist.Empty))
    exact Iff.mpr oneFactor productInverseSolution

 theorem field_product_right_mul_equation_exact_from_apartness
    {mul : BHist -> BHist -> BHist} {one : BHist} {NonZero : BHist -> Prop}
    {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b x c : BHist} (pab : NonZero (mul a b)) (pa : NonZero a) (pb : NonZero b) :
    hsame (mul x (mul a b)) (append BHist.Empty c) ↔
      hsame x (mul (append BHist.Empty c) (mul (inv b pb) (inv a pa))) := by
  have oneFactor :
      hsame (mul x (mul a b)) (append BHist.Empty c) ↔
        hsame x (mul (append BHist.Empty c) (inv (mul a b) pab)) := by
    exact field_right_mul_equation_exact_from_apartness
      assocC rightId mulCongr leftInv rightInv pab
  have reverseInverse :
      hsame (inv (mul a b) pab) (mul (inv b pb) (inv a pa)) := by
    exact field_inverse_product_reverse_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv pab pa pb
  constructor
  · intro productEndpoint
    exact hsame_trans (Iff.mp oneFactor productEndpoint)
      (mulCongr (hsame_refl (append BHist.Empty c)) reverseInverse)
  · intro reversedSolution
    have productInverseSolution :
        hsame x (mul (append BHist.Empty c) (inv (mul a b) pab)) := by
      exact hsame_trans reversedSolution
        (mulCongr (hsame_refl (append BHist.Empty c)) (hsame_symm reverseInverse))
    exact Iff.mpr oneFactor productInverseSolution

 theorem field_product_left_mul_equation_exact_from_apartness
    {mul : BHist -> BHist -> BHist} {one : BHist} {NonZero : BHist -> Prop}
    {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b x c : BHist} (pab : NonZero (mul a b)) (pa : NonZero a) (pb : NonZero b) :
    hsame (mul (mul a b) x) (append BHist.Empty c) <->
      hsame x (mul (mul (inv b pb) (inv a pa)) (append BHist.Empty c)) := by
  have oneFactor :
      hsame (mul (mul a b) x) (append BHist.Empty c) <->
        hsame x (mul (inv (mul a b) pab) (append BHist.Empty c)) := by
    exact field_left_mul_equation_exact_from_apartness
      assocC leftId mulCongr leftInv rightInv pab
  have reverseInverse :
      hsame (inv (mul a b) pab) (mul (inv b pb) (inv a pa)) := by
    exact field_inverse_product_reverse_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv pab pa pb
  constructor
  · intro productEndpoint
    exact hsame_trans (Iff.mp oneFactor productEndpoint)
      (mulCongr reverseInverse (hsame_refl (append BHist.Empty c)))
  · intro reversedSolution
    have productInverseSolution :
        hsame x (mul (inv (mul a b) pab) (append BHist.Empty c)) := by
      exact hsame_trans reversedSolution
        (mulCongr (hsame_symm reverseInverse) (hsame_refl (append BHist.Empty c)))
    exact Iff.mpr oneFactor productInverseSolution

 theorem field_product_right_mul_empty_context_solution_deterministic_from_apartness
    {mul : BHist -> BHist -> BHist} {one : BHist} {NonZero : BHist -> Prop}
    {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b x y c : BHist} (pab : NonZero (mul a b)) (pa : NonZero a)
    (pb : NonZero b) :
    hsame (mul x (mul a b)) (append BHist.Empty c) ->
      hsame (mul y (mul a b)) (append BHist.Empty c) -> hsame x y := by
  intro xEquation yEquation
  have xExact :
      hsame (mul x (mul a b)) (append BHist.Empty c) <->
        hsame x (mul (append BHist.Empty c) (mul (inv b pb) (inv a pa))) := by
    exact field_product_right_mul_equation_exact_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv pab pa pb
  have yExact :
      hsame (mul y (mul a b)) (append BHist.Empty c) <->
        hsame y (mul (append BHist.Empty c) (mul (inv b pb) (inv a pa))) := by
    exact field_product_right_mul_equation_exact_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv pab pa pb
  exact hsame_trans (Iff.mp xExact xEquation) (hsame_symm (Iff.mp yExact yEquation))

 theorem field_product_left_mul_empty_context_solution_deterministic_from_apartness
    {mul : BHist -> BHist -> BHist} {one : BHist} {NonZero : BHist -> Prop}
    {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b x y c : BHist} (pab : NonZero (mul a b)) (pa : NonZero a)
    (pb : NonZero b) :
    hsame (mul (mul a b) x) (append BHist.Empty c) ->
      hsame (mul (mul a b) y) (append BHist.Empty c) -> hsame x y := by
  intro xEquation yEquation
  have xExact :
      hsame (mul (mul a b) x) (append BHist.Empty c) <->
        hsame x (mul (mul (inv b pb) (inv a pa)) (append BHist.Empty c)) := by
    exact field_product_left_mul_equation_exact_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv pab pa pb
  have yExact :
      hsame (mul (mul a b) y) (append BHist.Empty c) <->
        hsame y (mul (mul (inv b pb) (inv a pa)) (append BHist.Empty c)) := by
    exact field_product_left_mul_equation_exact_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv pab pa pb
  exact hsame_trans (Iff.mp xExact xEquation) (hsame_symm (Iff.mp yExact yEquation))

 theorem field_product_factor_map_empty_context_classifier_exact_from_apartness
    {mul : BHist -> BHist -> BHist} {one : BHist} {NonZero : BHist -> Prop}
    {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b x y : BHist} (pab : NonZero (mul a b)) (pa : NonZero a) (pb : NonZero b) :
    (hsame (mul x (mul a b)) (append BHist.Empty (mul y (mul a b))) <-> hsame x y) /\
      (hsame (mul (mul a b) x) (append BHist.Empty (mul (mul a b) y)) <->
        hsame x y) := by
  have rightExactX :
      hsame (mul x (mul a b)) (append BHist.Empty (mul y (mul a b))) <->
        hsame x
          (mul (append BHist.Empty (mul y (mul a b)))
            (mul (inv b pb) (inv a pa))) := by
    exact field_product_right_mul_equation_exact_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv pab pa pb
  have rightExactY :
      hsame (mul y (mul a b)) (append BHist.Empty (mul y (mul a b))) <->
        hsame y
          (mul (append BHist.Empty (mul y (mul a b)))
            (mul (inv b pb) (inv a pa))) := by
    exact field_product_right_mul_equation_exact_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv pab pa pb
  have rightEndpoint :
      hsame (mul y (mul a b)) (append BHist.Empty (mul y (mul a b))) := by
    exact hsame_symm (append_empty_left (mul y (mul a b)))
  have rightSolutionY :
      hsame y
        (mul (append BHist.Empty (mul y (mul a b))) (mul (inv b pb) (inv a pa))) := by
    exact Iff.mp rightExactY rightEndpoint
  have leftExactX :
      hsame (mul (mul a b) x) (append BHist.Empty (mul (mul a b) y)) <->
        hsame x
          (mul (mul (inv b pb) (inv a pa))
            (append BHist.Empty (mul (mul a b) y))) := by
    exact field_product_left_mul_equation_exact_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv pab pa pb
  have leftExactY :
      hsame (mul (mul a b) y) (append BHist.Empty (mul (mul a b) y)) <->
        hsame y
          (mul (mul (inv b pb) (inv a pa))
            (append BHist.Empty (mul (mul a b) y))) := by
    exact field_product_left_mul_equation_exact_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv pab pa pb
  have leftEndpoint :
      hsame (mul (mul a b) y) (append BHist.Empty (mul (mul a b) y)) := by
    exact hsame_symm (append_empty_left (mul (mul a b) y))
  have leftSolutionY :
      hsame y
        (mul (mul (inv b pb) (inv a pa)) (append BHist.Empty (mul (mul a b) y))) := by
    exact Iff.mp leftExactY leftEndpoint
  constructor
  · constructor
    · intro sameProducts
      exact hsame_trans (Iff.mp rightExactX sameProducts) (hsame_symm rightSolutionY)
    · intro sameXY
      exact hsame_trans (mulCongr sameXY (hsame_refl (mul a b))) rightEndpoint
  · constructor
    · intro sameProducts
      exact hsame_trans (Iff.mp leftExactX sameProducts) (hsame_symm leftSolutionY)
    · intro sameXY
      exact hsame_trans (mulCongr (hsame_refl (mul a b)) sameXY) leftEndpoint

end BEDC.Derived.FieldUp
