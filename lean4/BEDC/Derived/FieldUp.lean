import BEDC.FKernel.Hist
import BEDC.Derived.GroupUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

theorem field_inverse_congruence_from_apartness {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b : BHist} (sameAB : hsame a b) (p : NonZero a) (q : NonZero b) :
    hsame (inv a p) (inv b q) := by
  have transportedLeft : hsame (mul (inv a p) b) one := by
    exact hsame_trans
      (hsame_symm (mulCongr (hsame_refl (inv a p)) sameAB))
      (leftInv a p)
  exact BEDC.Derived.GroupUp.group_left_right_inverse_uniqueness
    assocC
    leftId
    rightId
    mulCongr
    transportedLeft
    (rightInv b q)

theorem field_inverse_cancel_from_apartness {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b : BHist} (p : NonZero a) (q : NonZero b) :
    hsame (inv a p) (inv b q) -> hsame a b := by
  intro sameInv
  have transportedLeft : hsame (mul (inv b q) a) one := by
    exact hsame_trans
      (hsame_symm (mulCongr sameInv (hsame_refl a)))
      (leftInv a p)
  exact hsame_symm
    (BEDC.Derived.GroupUp.group_left_right_inverse_uniqueness
      assocC
      leftId
      rightId
      mulCongr
      (rightInv b q)
      transportedLeft)

 theorem field_inverse_product_reverse_from_apartness {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b : BHist} (pab : NonZero (mul a b)) (pa : NonZero a) (pb : NonZero b) :
    hsame (inv (mul a b) pab) (mul (inv b pb) (inv a pa)) := by
  have reverseRight : hsame (mul (mul a b) (mul (inv b pb) (inv a pa))) one := by
    have inner :
        hsame (mul b (mul (inv b pb) (inv a pa))) (inv a pa) := by
      exact hsame_trans (hsame_symm (assocC b (inv b pb) (inv a pa)))
        (hsame_trans (mulCongr (rightInv b pb) (hsame_refl (inv a pa)))
          (leftId (inv a pa)))
    exact hsame_trans (assocC a b (mul (inv b pb) (inv a pa)))
      (hsame_trans (mulCongr (hsame_refl a) inner) (rightInv a pa))
  exact BEDC.Derived.GroupUp.group_left_right_inverse_uniqueness
    assocC
    leftId
    rightId
    mulCongr
    (leftInv (mul a b) pab)
    reverseRight

 theorem field_mul_inverse_right_cancel_from_apartness {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one) :
    forall (a b : BHist) (pb : NonZero b),
      hsame (mul (mul a b) (inv b pb)) a := by
  intro a b pb
  have reassoc :
      hsame (mul (mul a b) (inv b pb)) (mul a (mul b (inv b pb))) := by
    exact assocC a b (inv b pb)
  have cancelTail : hsame (mul a (mul b (inv b pb))) (mul a one) := by
    exact mulCongr (hsame_refl a) (rightInv b pb)
  exact hsame_trans reassoc (hsame_trans cancelTail (rightId a))

 theorem field_right_mul_equation_solution_from_apartness {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {x b a : BHist} (pb : NonZero b) :
    hsame (mul x b) a -> hsame x (mul a (inv b pb)) := by
  intro sameProduct
  exact hsame_trans
    (hsame_symm
      (field_mul_inverse_right_cancel_from_apartness assocC rightId mulCongr rightInv x b pb))
    (mulCongr sameProduct (hsame_refl (inv b pb)))

 theorem field_right_mul_equation_solution_from_apartness_iff {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {x b a : BHist} (pb : NonZero b) :
    hsame (mul x b) a <-> hsame x (mul a (inv b pb)) := by
  constructor
  · intro sameProduct
    exact field_right_mul_equation_solution_from_apartness
      assocC rightId mulCongr rightInv pb sameProduct
  · intro sameSolution
    have transported :
        hsame (mul x b) (mul (mul a (inv b pb)) b) := by
      exact mulCongr sameSolution (hsame_refl b)
    have reassoc :
        hsame (mul (mul a (inv b pb)) b) (mul a (mul (inv b pb) b)) := by
      exact assocC a (inv b pb) b
    have cancelTail :
        hsame (mul a (mul (inv b pb) b)) (mul a one) := by
      exact mulCongr (hsame_refl a) (leftInv b pb)
    exact hsame_trans transported
      (hsame_trans reassoc (hsame_trans cancelTail (rightId a)))

 theorem field_mul_inverse_left_cancel_from_apartness {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one) :
    forall (a b : BHist) (pa : NonZero a),
      hsame (mul (inv a pa) (mul a b)) b := by
  intro a b pa
  have reassoc :
      hsame (mul (inv a pa) (mul a b)) (mul (mul (inv a pa) a) b) := by
    exact hsame_symm (assocC (inv a pa) a b)
  have cancelHead : hsame (mul (mul (inv a pa) a) b) (mul one b) := by
    exact mulCongr (leftInv a pa) (hsame_refl b)
  exact hsame_trans reassoc (hsame_trans cancelHead (leftId b))

 theorem field_middle_mul_equation_solution_from_apartness {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a x b c : BHist} (pa : NonZero a) (pb : NonZero b) :
    hsame (mul (mul a x) b) c -> hsame x (mul (inv a pa) (mul c (inv b pb))) := by
  intro sameProduct
  have solveRight : hsame (mul a x) (mul c (inv b pb)) := by
    exact field_right_mul_equation_solution_from_apartness
      assocC rightId mulCongr rightInv pb sameProduct
  exact hsame_trans
    (hsame_symm (field_mul_inverse_left_cancel_from_apartness
      assocC leftId mulCongr leftInv a x pa))
    (mulCongr (hsame_refl (inv a pa)) solveRight)

 theorem field_middle_mul_equation_solution_from_apartness_iff {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a x b c : BHist} (pa : NonZero a) (pb : NonZero b) :
    hsame (mul (mul a x) b) c <-> hsame x (mul (inv a pa) (mul c (inv b pb))) := by
  constructor
  · intro sameProduct
    exact field_middle_mul_equation_solution_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv pa pb sameProduct
  · intro sameSolution
    let tail := mul c (inv b pb)
    have leftTransport :
        hsame (mul a x) (mul a (mul (inv a pa) tail)) := by
      exact mulCongr (hsame_refl a) sameSolution
    have exposeLeft :
        hsame (mul a (mul (inv a pa) tail)) (mul (mul a (inv a pa)) tail) := by
      exact hsame_symm (assocC a (inv a pa) tail)
    have cancelLeft :
        hsame (mul (mul a (inv a pa)) tail) (mul one tail) := by
      exact mulCongr (rightInv a pa) (hsame_refl tail)
    have collapseLeft :
        hsame (mul a x) tail := by
      exact hsame_trans leftTransport
        (hsame_trans exposeLeft (hsame_trans cancelLeft (leftId tail)))
    have multiplyRight :
        hsame (mul (mul a x) b) (mul tail b) := by
      exact mulCongr collapseLeft (hsame_refl b)
    have exposeRight :
        hsame (mul tail b) (mul c (mul (inv b pb) b)) := by
      exact assocC c (inv b pb) b
    have cancelRight :
        hsame (mul c (mul (inv b pb) b)) (mul c one) := by
      exact mulCongr (hsame_refl c) (leftInv b pb)
    exact hsame_trans multiplyRight
      (hsame_trans exposeRight (hsame_trans cancelRight (rightId c)))

end BEDC.Derived.FieldUp
