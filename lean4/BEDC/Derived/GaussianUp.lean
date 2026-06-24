import BEDC.Derived.IntUp.CommRing

namespace BEDC.Derived.GaussianUp

abbrev Z := BEDC.Derived.PrimeUp.IntegerUp
abbrev Zeq := BEDC.Derived.RationalUp.IntEq
abbrev Zadd := BEDC.Derived.RationalUp.IntAdd
abbrev Zmul := BEDC.Derived.RationalUp.IntMul
abbrev Zneg := BEDC.Derived.RationalUp.IntNeg
abbrev Zzero := BEDC.Derived.RationalUp.intZero
abbrev Zone := BEDC.Derived.RationalUp.intOne

private def zlaws : BEDC.Derived.IntUp.IntegerUpCommRingLaws :=
  BEDC.Derived.IntUp.IntegerUp_comm_ring_laws

structure GaussInt where
  re : Z
  im : Z

def GaussEq (z w : GaussInt) : Prop :=
  Zeq z.re w.re ∧ Zeq z.im w.im

def gaussZero : GaussInt :=
  { re := Zzero, im := Zzero }

def gaussOne : GaussInt :=
  { re := Zone, im := Zzero }

def gaussAdd (z w : GaussInt) : GaussInt :=
  { re := Zadd z.re w.re,
    im := Zadd z.im w.im }

def gaussNeg (z : GaussInt) : GaussInt :=
  { re := Zneg z.re,
    im := Zneg z.im }

def gaussMul (z w : GaussInt) : GaussInt :=
  { re := Zadd (Zmul z.re w.re) (Zneg (Zmul z.im w.im)),
    im := Zadd (Zmul z.re w.im) (Zmul z.im w.re) }

def gaussConj (z : GaussInt) : GaussInt :=
  { re := z.re, im := Zneg z.im }

def gaussNorm (z : GaussInt) : Z :=
  Zadd (Zmul z.re z.re) (Zmul z.im z.im)

def gaussOfInt (x : Z) : GaussInt :=
  { re := x, im := Zzero }

private theorem zadd_right {a b c : Z} (h : Zeq a b) :
    Zeq (Zadd a c) (Zadd b c) :=
  zlaws.add_respects h (zlaws.eq_refl c)

private theorem zadd_left {a b c : Z} (h : Zeq a b) :
    Zeq (Zadd c a) (Zadd c b) :=
  zlaws.add_respects (zlaws.eq_refl c) h

private theorem zmul_right {a b c : Z} (h : Zeq a b) :
    Zeq (Zmul a c) (Zmul b c) :=
  zlaws.mul_respects h (zlaws.eq_refl c)

private theorem zmul_left {a b c : Z} (h : Zeq a b) :
    Zeq (Zmul c a) (Zmul c b) :=
  zlaws.mul_respects (zlaws.eq_refl c) h

private theorem zneg_zero :
    Zeq (Zneg Zzero) Zzero :=
  zlaws.eq_trans
    (zlaws.eq_symm (zlaws.zero_add (Zneg Zzero)))
    (zlaws.add_neg Zzero)

private theorem zadd_four_swap (a b c d : Z) :
    Zeq (Zadd (Zadd a b) (Zadd c d))
      (Zadd (Zadd a c) (Zadd b d)) := by
  exact zlaws.eq_trans (zlaws.add_assoc a b (Zadd c d))
    (zlaws.eq_trans
      (zadd_left (a := Zadd b (Zadd c d))
        (b := Zadd (Zadd b c) d)
        (c := a)
        (zlaws.eq_symm (zlaws.add_assoc b c d)))
      (zlaws.eq_trans
        (zadd_left (a := Zadd (Zadd b c) d)
          (b := Zadd (Zadd c b) d)
          (c := a)
          (zadd_right (a := Zadd b c) (b := Zadd c b) (c := d)
            (zlaws.add_comm b c)))
        (zlaws.eq_trans
          (zadd_left (a := Zadd (Zadd c b) d)
            (b := Zadd c (Zadd b d))
            (c := a)
            (zlaws.add_assoc c b d))
          (zlaws.eq_symm (zlaws.add_assoc a c (Zadd b d))))))

private theorem zadd_four_last_swap (a b c d : Z) :
    Zeq (Zadd (Zadd a b) (Zadd c d))
      (Zadd (Zadd a d) (Zadd c b)) := by
  exact zlaws.eq_trans
    (zadd_left (a := Zadd c d) (b := Zadd d c) (c := Zadd a b)
      (zlaws.add_comm c d))
    (zlaws.eq_trans (zadd_four_swap a b d c)
      (zadd_left (a := Zadd b c) (b := Zadd c b) (c := Zadd a d)
        (zlaws.add_comm b c)))

private theorem z_eq_neg_of_add_eq_zero {a b : Z} :
    Zeq (Zadd a b) Zzero -> Zeq b (Zneg a) := by
  intro h
  exact zlaws.eq_trans (zlaws.eq_symm (zlaws.zero_add b))
    (zlaws.eq_trans
      (zadd_right (a := Zzero) (b := Zadd (Zneg a) a) (c := b)
        (zlaws.eq_symm (zlaws.neg_add a)))
      (zlaws.eq_trans (zlaws.add_assoc (Zneg a) a b)
        (zlaws.eq_trans (zadd_left (a := Zadd a b) (b := Zzero) (c := Zneg a) h)
          (zlaws.add_zero (Zneg a)))))

private theorem zneg_neg (a : Z) :
    Zeq (Zneg (Zneg a)) a :=
  zlaws.eq_symm
    (z_eq_neg_of_add_eq_zero (a := Zneg a) (b := a) (zlaws.neg_add a))

private theorem zneg_add (a b : Z) :
    Zeq (Zneg (Zadd a b)) (Zadd (Zneg a) (Zneg b)) := by
  have hzero :
      Zeq (Zadd (Zadd a b) (Zadd (Zneg a) (Zneg b))) Zzero := by
    exact zlaws.eq_trans (zadd_four_swap a b (Zneg a) (Zneg b))
      (zlaws.eq_trans
        (zlaws.add_respects (zlaws.add_neg a) (zlaws.add_neg b))
        (zlaws.add_zero Zzero))
  exact zlaws.eq_symm
    (z_eq_neg_of_add_eq_zero (a := Zadd a b)
      (b := Zadd (Zneg a) (Zneg b)) hzero)

private theorem zmul_neg_right (a b : Z) :
    Zeq (Zmul a (Zneg b)) (Zneg (Zmul a b)) := by
  have hzero :
      Zeq (Zadd (Zmul a b) (Zmul a (Zneg b))) Zzero := by
    exact zlaws.eq_trans
      (zlaws.eq_symm (zlaws.left_distrib a b (Zneg b)))
      (zlaws.eq_trans
        (zlaws.mul_respects (zlaws.eq_refl a) (zlaws.add_neg b))
        (zlaws.mul_zero a))
  exact z_eq_neg_of_add_eq_zero (a := Zmul a b) (b := Zmul a (Zneg b)) hzero

private theorem zmul_neg_left (a b : Z) :
    Zeq (Zmul (Zneg a) b) (Zneg (Zmul a b)) := by
  exact zlaws.eq_trans (zlaws.mul_comm (Zneg a) b)
    (zlaws.eq_trans (zmul_neg_right b a)
      (zlaws.neg_respects (zlaws.mul_comm b a)))

private theorem zmul_neg_neg (a b : Z) :
    Zeq (Zmul (Zneg a) (Zneg b)) (Zmul a b) := by
  exact zlaws.eq_trans (zmul_neg_left a (Zneg b))
    (zlaws.eq_trans
      (zlaws.neg_respects (zmul_neg_right a b))
      (zneg_neg (Zmul a b)))

private def zsub (a b : Z) : Z :=
  Zadd a (Zneg b)

private theorem zsub_respects {a a' b b' : Z} :
    Zeq a a' -> Zeq b b' -> Zeq (zsub a b) (zsub a' b') := by
  intro ha hb
  exact zlaws.add_respects ha (zlaws.neg_respects hb)

private theorem zmul_sub_left (a b c : Z) :
    Zeq (Zmul a (zsub b c)) (zsub (Zmul a b) (Zmul a c)) := by
  exact zlaws.eq_trans (zlaws.left_distrib a b (Zneg c))
    (zadd_left (a := Zmul a (Zneg c))
      (b := Zneg (Zmul a c))
      (c := Zmul a b)
      (zmul_neg_right a c))

private theorem zmul_sub_right (a b c : Z) :
    Zeq (Zmul (zsub a b) c) (zsub (Zmul a c) (Zmul b c)) := by
  exact zlaws.eq_trans (zlaws.right_distrib a (Zneg b) c)
    (zadd_left (a := Zmul (Zneg b) c)
      (b := Zneg (Zmul b c))
      (c := Zmul a c)
      (zmul_neg_left b c))

private theorem zsub_add_sub (a b c d : Z) :
    Zeq (zsub (Zadd a b) (Zadd c d))
      (Zadd (zsub a c) (zsub b d)) := by
  exact zlaws.eq_trans
    (zadd_left (a := Zneg (Zadd c d))
      (b := Zadd (Zneg c) (Zneg d))
      (c := Zadd a b)
      (zneg_add c d))
    (zadd_four_swap a b (Zneg c) (Zneg d))

private theorem zsub_sub_pair_rotate (x y u v : Z) :
    Zeq (zsub (zsub x y) (Zadd u v))
      (zsub (zsub x u) (Zadd v y)) := by
  exact zlaws.eq_trans
    (zadd_left (a := Zneg (Zadd u v))
      (b := Zadd (Zneg u) (Zneg v))
      (c := zsub x y)
      (zneg_add u v))
    (zlaws.eq_trans (zadd_four_swap x (Zneg y) (Zneg u) (Zneg v))
      (zlaws.eq_trans
        (zadd_left (a := Zadd (Zneg y) (Zneg v))
          (b := Zadd (Zneg v) (Zneg y))
          (c := zsub x u)
          (zlaws.add_comm (Zneg y) (Zneg v)))
        (zadd_left (a := Zadd (Zneg v) (Zneg y))
          (b := Zneg (Zadd v y))
          (c := zsub x u)
          (zlaws.eq_symm (zneg_add v y)))))

private theorem zsub_add_pair_swap (x y u v : Z) :
    Zeq (Zadd (zsub x y) (Zadd u v))
      (Zadd (Zadd x u) (zsub v y)) := by
  exact zlaws.eq_trans (zadd_four_swap x (Zneg y) u v)
    (zadd_left (a := Zadd (Zneg y) v)
      (b := Zadd v (Zneg y))
      (c := Zadd x u)
      (zlaws.add_comm (Zneg y) v))

private theorem gaussMul_assoc_re_expr (a b c d e f : Z) :
    Zeq
      (zsub (Zmul (zsub (Zmul a c) (Zmul b d)) e)
        (Zmul (Zadd (Zmul a d) (Zmul b c)) f))
      (zsub (Zmul a (zsub (Zmul c e) (Zmul d f)))
        (Zmul b (Zadd (Zmul c f) (Zmul d e)))) := by
  have leftStructured :
      Zeq
        (zsub (Zmul (zsub (Zmul a c) (Zmul b d)) e)
          (Zmul (Zadd (Zmul a d) (Zmul b c)) f))
        (zsub (zsub (Zmul (Zmul a c) e) (Zmul (Zmul b d) e))
          (Zadd (Zmul (Zmul a d) f) (Zmul (Zmul b c) f))) :=
    zsub_respects
      (zmul_sub_right (Zmul a c) (Zmul b d) e)
      (zlaws.right_distrib (Zmul a d) (Zmul b c) f)
  have rightStructured :
      Zeq
        (zsub (Zmul a (zsub (Zmul c e) (Zmul d f)))
          (Zmul b (Zadd (Zmul c f) (Zmul d e))))
        (zsub (zsub (Zmul (Zmul a c) e) (Zmul (Zmul a d) f))
          (Zadd (Zmul (Zmul b c) f) (Zmul (Zmul b d) e))) :=
    zsub_respects
      (zlaws.eq_trans (zmul_sub_left a (Zmul c e) (Zmul d f))
        (zsub_respects
          (zlaws.eq_symm (zlaws.mul_assoc a c e))
          (zlaws.eq_symm (zlaws.mul_assoc a d f))))
      (zlaws.eq_trans (zlaws.left_distrib b (Zmul c f) (Zmul d e))
        (zlaws.add_respects
          (zlaws.eq_symm (zlaws.mul_assoc b c f))
          (zlaws.eq_symm (zlaws.mul_assoc b d e))))
  exact zlaws.eq_trans leftStructured
    (zlaws.eq_trans
      (zsub_sub_pair_rotate
        (Zmul (Zmul a c) e) (Zmul (Zmul b d) e)
        (Zmul (Zmul a d) f) (Zmul (Zmul b c) f))
      (zlaws.eq_symm rightStructured))

private theorem gaussMul_assoc_im_expr (a b c d e f : Z) :
    Zeq
      (Zadd (Zmul (zsub (Zmul a c) (Zmul b d)) f)
        (Zmul (Zadd (Zmul a d) (Zmul b c)) e))
      (Zadd (Zmul a (Zadd (Zmul c f) (Zmul d e)))
        (Zmul b (zsub (Zmul c e) (Zmul d f)))) := by
  have leftStructured :
      Zeq
        (Zadd (Zmul (zsub (Zmul a c) (Zmul b d)) f)
          (Zmul (Zadd (Zmul a d) (Zmul b c)) e))
        (Zadd (zsub (Zmul (Zmul a c) f) (Zmul (Zmul b d) f))
          (Zadd (Zmul (Zmul a d) e) (Zmul (Zmul b c) e))) :=
    zlaws.add_respects
      (zmul_sub_right (Zmul a c) (Zmul b d) f)
      (zlaws.right_distrib (Zmul a d) (Zmul b c) e)
  have rightStructured :
      Zeq
        (Zadd (Zmul a (Zadd (Zmul c f) (Zmul d e)))
          (Zmul b (zsub (Zmul c e) (Zmul d f))))
        (Zadd (Zadd (Zmul (Zmul a c) f) (Zmul (Zmul a d) e))
          (zsub (Zmul (Zmul b c) e) (Zmul (Zmul b d) f))) :=
    zlaws.add_respects
      (zlaws.eq_trans (zlaws.left_distrib a (Zmul c f) (Zmul d e))
        (zlaws.add_respects
          (zlaws.eq_symm (zlaws.mul_assoc a c f))
          (zlaws.eq_symm (zlaws.mul_assoc a d e))))
      (zlaws.eq_trans (zmul_sub_left b (Zmul c e) (Zmul d f))
        (zsub_respects
          (zlaws.eq_symm (zlaws.mul_assoc b c e))
          (zlaws.eq_symm (zlaws.mul_assoc b d f))))
  exact zlaws.eq_trans leftStructured
    (zlaws.eq_trans
      (zsub_add_pair_swap
        (Zmul (Zmul a c) f) (Zmul (Zmul b d) f)
        (Zmul (Zmul a d) e) (Zmul (Zmul b c) e))
      (zlaws.eq_symm rightStructured))

private theorem gaussMul_add_distrib_re_expr (a b c d e f : Z) :
    Zeq
      (zsub (Zmul a (Zadd c e)) (Zmul b (Zadd d f)))
      (Zadd (zsub (Zmul a c) (Zmul b d))
        (zsub (Zmul a e) (Zmul b f))) := by
  exact zlaws.eq_trans
    (zsub_respects
      (zlaws.left_distrib a c e)
      (zlaws.left_distrib b d f))
    (zsub_add_sub (Zmul a c) (Zmul a e) (Zmul b d) (Zmul b f))

private theorem gaussMul_add_distrib_im_expr (a b c d e f : Z) :
    Zeq
      (Zadd (Zmul a (Zadd d f)) (Zmul b (Zadd c e)))
      (Zadd (Zadd (Zmul a d) (Zmul b c))
        (Zadd (Zmul a f) (Zmul b e))) := by
  exact zlaws.eq_trans
    (zlaws.add_respects
      (zlaws.left_distrib a d f)
      (zlaws.left_distrib b c e))
    (zadd_four_swap (Zmul a d) (Zmul a f) (Zmul b c) (Zmul b e))

theorem GaussEq_refl (z : GaussInt) :
    GaussEq z z := by
  constructor
  · exact zlaws.eq_refl z.re
  · exact zlaws.eq_refl z.im

theorem GaussEq_symm {z w : GaussInt} :
    GaussEq z w -> GaussEq w z := by
  intro h
  constructor
  · exact zlaws.eq_symm h.left
  · exact zlaws.eq_symm h.right

theorem GaussEq_trans {x y z : GaussInt} :
    GaussEq x y -> GaussEq y z -> GaussEq x z := by
  intro xy yz
  constructor
  · exact zlaws.eq_trans xy.left yz.left
  · exact zlaws.eq_trans xy.right yz.right

theorem gaussAdd_respects {x x' y y' : GaussInt} :
    GaussEq x x' -> GaussEq y y' ->
      GaussEq (gaussAdd x y) (gaussAdd x' y') := by
  intro hx hy
  constructor
  · exact zlaws.add_respects hx.left hy.left
  · exact zlaws.add_respects hx.right hy.right

theorem gaussNeg_respects {x y : GaussInt} :
    GaussEq x y -> GaussEq (gaussNeg x) (gaussNeg y) := by
  intro h
  constructor
  · exact zlaws.neg_respects h.left
  · exact zlaws.neg_respects h.right

theorem gaussMul_respects {x x' y y' : GaussInt} :
    GaussEq x x' -> GaussEq y y' ->
      GaussEq (gaussMul x y) (gaussMul x' y') := by
  intro hx hy
  constructor
  · exact zlaws.add_respects
      (zlaws.mul_respects hx.left hy.left)
      (zlaws.neg_respects (zlaws.mul_respects hx.right hy.right))
  · exact zlaws.add_respects
      (zlaws.mul_respects hx.left hy.right)
      (zlaws.mul_respects hx.right hy.left)

theorem gaussAdd_comm (z w : GaussInt) :
    GaussEq (gaussAdd z w) (gaussAdd w z) := by
  constructor
  · exact zlaws.add_comm z.re w.re
  · exact zlaws.add_comm z.im w.im

theorem gaussAdd_assoc (x y z : GaussInt) :
    GaussEq (gaussAdd (gaussAdd x y) z)
      (gaussAdd x (gaussAdd y z)) := by
  constructor
  · exact zlaws.add_assoc x.re y.re z.re
  · exact zlaws.add_assoc x.im y.im z.im

theorem gaussAdd_zero (z : GaussInt) :
    GaussEq (gaussAdd z gaussZero) z := by
  constructor
  · exact zlaws.add_zero z.re
  · exact zlaws.add_zero z.im

theorem gaussAdd_zero_left (z : GaussInt) :
    GaussEq (gaussAdd gaussZero z) z := by
  constructor
  · exact zlaws.zero_add z.re
  · exact zlaws.zero_add z.im

theorem gaussAdd_neg (z : GaussInt) :
    GaussEq (gaussAdd z (gaussNeg z)) gaussZero := by
  constructor
  · exact zlaws.add_neg z.re
  · exact zlaws.add_neg z.im

theorem gaussAdd_neg_left (z : GaussInt) :
    GaussEq (gaussAdd (gaussNeg z) z) gaussZero := by
  constructor
  · exact zlaws.neg_add z.re
  · exact zlaws.neg_add z.im

theorem gaussMul_comm (z w : GaussInt) :
    GaussEq (gaussMul z w) (gaussMul w z) := by
  constructor
  · exact zlaws.add_respects
      (zlaws.mul_comm z.re w.re)
      (zlaws.neg_respects (zlaws.mul_comm z.im w.im))
  · exact zlaws.eq_trans
      (zlaws.add_respects
        (zlaws.mul_comm z.re w.im)
        (zlaws.mul_comm z.im w.re))
      (zlaws.add_comm (Zmul w.im z.re) (Zmul w.re z.im))

theorem gaussMul_assoc (x y z : GaussInt) :
    GaussEq (gaussMul (gaussMul x y) z)
      (gaussMul x (gaussMul y z)) := by
  constructor
  · exact gaussMul_assoc_re_expr x.re x.im y.re y.im z.re z.im
  · exact gaussMul_assoc_im_expr x.re x.im y.re y.im z.re z.im

theorem gaussMul_add_distrib (x y z : GaussInt) :
    GaussEq (gaussMul x (gaussAdd y z))
      (gaussAdd (gaussMul x y) (gaussMul x z)) := by
  constructor
  · exact gaussMul_add_distrib_re_expr x.re x.im y.re y.im z.re z.im
  · exact gaussMul_add_distrib_im_expr x.re x.im y.re y.im z.re z.im

theorem gaussMul_add_distrib_right (x y z : GaussInt) :
    GaussEq (gaussMul (gaussAdd x y) z)
      (gaussAdd (gaussMul x z) (gaussMul y z)) := by
  exact GaussEq_trans (gaussMul_comm (gaussAdd x y) z)
    (GaussEq_trans (gaussMul_add_distrib z x y)
      (gaussAdd_respects (gaussMul_comm z x) (gaussMul_comm z y)))

theorem gaussMul_zero (z : GaussInt) :
    GaussEq (gaussMul z gaussZero) gaussZero := by
  constructor
  · exact zlaws.eq_trans
      (zlaws.add_respects
        (zlaws.mul_zero z.re)
        (zlaws.neg_respects (zlaws.mul_zero z.im)))
      (zlaws.eq_trans
        (zadd_left (a := Zneg Zzero) (b := Zzero) (c := Zzero) zneg_zero)
        (zlaws.add_zero Zzero))
  · exact zlaws.eq_trans
      (zlaws.add_respects
        (zlaws.mul_zero z.re)
        (zlaws.mul_zero z.im))
      (zlaws.add_zero Zzero)

theorem gaussMul_zero_left (z : GaussInt) :
    GaussEq (gaussMul gaussZero z) gaussZero :=
  GaussEq_trans (gaussMul_comm gaussZero z) (gaussMul_zero z)

theorem gaussMul_one (z : GaussInt) :
    GaussEq (gaussMul z gaussOne) z := by
  constructor
  · exact zlaws.eq_trans
      (zlaws.add_respects
        (zlaws.mul_one z.re)
        (zlaws.neg_respects (zlaws.mul_zero z.im)))
      (zlaws.eq_trans
        (zadd_left (a := Zneg Zzero) (b := Zzero) (c := z.re) zneg_zero)
        (zlaws.add_zero z.re))
  · exact zlaws.eq_trans
      (zlaws.add_respects
        (zlaws.mul_zero z.re)
        (zlaws.mul_one z.im))
      (zlaws.zero_add z.im)

theorem gaussMul_one_left (z : GaussInt) :
    GaussEq (gaussMul gaussOne z) z :=
  GaussEq_trans (gaussMul_comm gaussOne z) (gaussMul_one z)

theorem gaussConj_respects {z w : GaussInt} :
    GaussEq z w -> GaussEq (gaussConj z) (gaussConj w) := by
  intro h
  constructor
  · exact h.left
  · exact zlaws.neg_respects h.right

theorem gaussConj_involutive (z : GaussInt) :
    GaussEq (gaussConj (gaussConj z)) z := by
  constructor
  · exact zlaws.eq_refl z.re
  · exact zneg_neg z.im

theorem gaussConj_mul (z w : GaussInt) :
    GaussEq (gaussConj (gaussMul z w))
      (gaussMul (gaussConj z) (gaussConj w)) := by
  constructor
  · exact zlaws.eq_symm
      (zlaws.add_respects
        (zlaws.eq_refl (Zmul z.re w.re))
        (zlaws.neg_respects (zmul_neg_neg z.im w.im)))
  · have first :
        Zeq (Zneg (Zadd (Zmul z.re w.im) (Zmul z.im w.re)))
          (Zadd (Zneg (Zmul z.re w.im)) (Zneg (Zmul z.im w.re))) :=
      zneg_add (Zmul z.re w.im) (Zmul z.im w.re)
    exact zlaws.eq_trans first
      (zlaws.add_respects
        (zlaws.eq_symm (zmul_neg_right z.re w.im))
        (zlaws.eq_symm (zmul_neg_left z.im w.re)))

theorem gaussMul_conj_norm (z : GaussInt) :
    GaussEq (gaussMul z (gaussConj z)) (gaussOfInt (gaussNorm z)) := by
  constructor
  · exact zlaws.eq_trans
      (zadd_left (a := Zneg (Zmul z.im (Zneg z.im)))
        (b := Zmul z.im z.im)
        (c := Zmul z.re z.re)
        (zlaws.eq_trans
          (zlaws.neg_respects (zmul_neg_right z.im z.im))
          (zneg_neg (Zmul z.im z.im))))
      (zlaws.eq_refl (Zadd (Zmul z.re z.re) (Zmul z.im z.im)))
  · exact zlaws.eq_trans
      (zlaws.add_respects
        (zmul_neg_right z.re z.im)
        (zlaws.eq_refl (Zmul z.im z.re)))
      (zlaws.eq_trans
        (zadd_right (a := Zneg (Zmul z.re z.im))
          (b := Zneg (Zmul z.im z.re))
          (c := Zmul z.im z.re)
          (zlaws.neg_respects (zlaws.mul_comm z.re z.im)))
        (zlaws.neg_add (Zmul z.im z.re)))

theorem gaussConj_mul_self_norm (z : GaussInt) :
    GaussEq (gaussMul (gaussConj z) z) (gaussOfInt (gaussNorm z)) :=
  GaussEq_trans (gaussMul_comm (gaussConj z) z) (gaussMul_conj_norm z)

theorem gaussOfInt_mul (a b : Z) :
    GaussEq (gaussMul (gaussOfInt a) (gaussOfInt b)) (gaussOfInt (Zmul a b)) := by
  constructor
  · exact zlaws.eq_trans
      (zadd_left (a := Zneg (Zmul Zzero Zzero))
        (b := Zzero)
        (c := Zmul a b)
        (zlaws.eq_trans (zlaws.neg_respects (zlaws.mul_zero Zzero)) zneg_zero))
      (zlaws.add_zero (Zmul a b))
  · exact zlaws.eq_trans
      (zlaws.add_respects (zlaws.mul_zero a) (zlaws.zero_mul b))
      (zlaws.add_zero Zzero)

theorem gaussNorm_respects {z w : GaussInt} :
    GaussEq z w -> Zeq (gaussNorm z) (gaussNorm w) := by
  intro h
  exact zlaws.add_respects
    (zlaws.mul_respects h.left h.left)
    (zlaws.mul_respects h.right h.right)

theorem gaussNorm_mul (z w : GaussInt) :
    Zeq (gaussNorm (gaussMul z w))
      (Zmul (gaussNorm z) (gaussNorm w)) := by
  let p := gaussMul z w
  have productNorm :
      GaussEq (gaussMul p (gaussConj p)) (gaussOfInt (gaussNorm p)) :=
    gaussMul_conj_norm p
  have conjProduct :
      GaussEq (gaussConj p) (gaussMul (gaussConj z) (gaussConj w)) := by
    exact gaussConj_mul z w
  have replaceConj :
      GaussEq (gaussMul p (gaussConj p))
        (gaussMul (gaussMul z w)
          (gaussMul (gaussConj z) (gaussConj w))) := by
    exact gaussMul_respects (GaussEq_refl p) conjProduct
  have reassocLeft :
      GaussEq (gaussMul (gaussMul z w)
          (gaussMul (gaussConj z) (gaussConj w)))
        (gaussMul z
          (gaussMul w (gaussMul (gaussConj z) (gaussConj w)))) :=
    gaussMul_assoc z w (gaussMul (gaussConj z) (gaussConj w))
  have moveConjZ :
      GaussEq
        (gaussMul w (gaussMul (gaussConj z) (gaussConj w)))
        (gaussMul (gaussConj z) (gaussMul w (gaussConj w))) := by
    exact GaussEq_trans
      (GaussEq_symm (gaussMul_assoc w (gaussConj z) (gaussConj w)))
      (GaussEq_trans
        (gaussMul_respects (gaussMul_comm w (gaussConj z))
          (GaussEq_refl (gaussConj w)))
        (gaussMul_assoc (gaussConj z) w (gaussConj w)))
  have reassocRight :
      GaussEq
        (gaussMul z
          (gaussMul (gaussConj z) (gaussMul w (gaussConj w))))
        (gaussMul (gaussMul z (gaussConj z))
          (gaussMul w (gaussConj w))) :=
    GaussEq_symm (gaussMul_assoc z (gaussConj z)
      (gaussMul w (gaussConj w)))
  have toNormFactors :
      GaussEq
        (gaussMul (gaussMul z w)
          (gaussMul (gaussConj z) (gaussConj w)))
        (gaussMul (gaussOfInt (gaussNorm z)) (gaussOfInt (gaussNorm w))) := by
    exact GaussEq_trans reassocLeft
      (GaussEq_trans (gaussMul_respects (GaussEq_refl z) moveConjZ)
        (GaussEq_trans reassocRight
          (gaussMul_respects (gaussMul_conj_norm z)
            (gaussMul_conj_norm w))))
  have productAsNorm :
      GaussEq (gaussOfInt (gaussNorm p))
        (gaussMul (gaussOfInt (gaussNorm z)) (gaussOfInt (gaussNorm w))) :=
    GaussEq_trans (GaussEq_symm productNorm)
      (GaussEq_trans replaceConj toNormFactors)
  have productAsInt :
      GaussEq (gaussMul (gaussOfInt (gaussNorm z)) (gaussOfInt (gaussNorm w)))
        (gaussOfInt (Zmul (gaussNorm z) (gaussNorm w))) :=
    gaussOfInt_mul (gaussNorm z) (gaussNorm w)
  exact zlaws.eq_trans productAsNorm.left productAsInt.left

structure GaussIntCommRingLaws where
  eq_refl : ∀ z : GaussInt, GaussEq z z
  eq_symm : ∀ {z w : GaussInt}, GaussEq z w -> GaussEq w z
  eq_trans :
    ∀ {x y z : GaussInt}, GaussEq x y -> GaussEq y z -> GaussEq x z
  add_respects :
    ∀ {x x' y y' : GaussInt}, GaussEq x x' -> GaussEq y y' ->
      GaussEq (gaussAdd x y) (gaussAdd x' y')
  mul_respects :
    ∀ {x x' y y' : GaussInt}, GaussEq x x' -> GaussEq y y' ->
      GaussEq (gaussMul x y) (gaussMul x' y')
  neg_respects :
    ∀ {x y : GaussInt}, GaussEq x y -> GaussEq (gaussNeg x) (gaussNeg y)
  add_comm : ∀ x y : GaussInt, GaussEq (gaussAdd x y) (gaussAdd y x)
  add_assoc :
    ∀ x y z : GaussInt,
      GaussEq (gaussAdd (gaussAdd x y) z) (gaussAdd x (gaussAdd y z))
  add_zero : ∀ x : GaussInt, GaussEq (gaussAdd x gaussZero) x
  zero_add : ∀ x : GaussInt, GaussEq (gaussAdd gaussZero x) x
  add_neg : ∀ x : GaussInt, GaussEq (gaussAdd x (gaussNeg x)) gaussZero
  neg_add : ∀ x : GaussInt, GaussEq (gaussAdd (gaussNeg x) x) gaussZero
  mul_comm : ∀ x y : GaussInt, GaussEq (gaussMul x y) (gaussMul y x)
  mul_assoc :
    ∀ x y z : GaussInt,
      GaussEq (gaussMul (gaussMul x y) z) (gaussMul x (gaussMul y z))
  mul_one : ∀ x : GaussInt, GaussEq (gaussMul x gaussOne) x
  one_mul : ∀ x : GaussInt, GaussEq (gaussMul gaussOne x) x
  mul_zero : ∀ x : GaussInt, GaussEq (gaussMul x gaussZero) gaussZero
  zero_mul : ∀ x : GaussInt, GaussEq (gaussMul gaussZero x) gaussZero
  left_distrib :
    ∀ x y z : GaussInt,
      GaussEq (gaussMul x (gaussAdd y z))
        (gaussAdd (gaussMul x y) (gaussMul x z))
  right_distrib :
    ∀ x y z : GaussInt,
      GaussEq (gaussMul (gaussAdd x y) z)
        (gaussAdd (gaussMul x z) (gaussMul y z))

def GaussInt_comm_ring_laws : GaussIntCommRingLaws where
  eq_refl := GaussEq_refl
  eq_symm := by
    intro z w
    exact GaussEq_symm
  eq_trans := by
    intro x y z
    exact GaussEq_trans
  add_respects := by
    intro x x' y y'
    exact gaussAdd_respects
  mul_respects := by
    intro x x' y y'
    exact gaussMul_respects
  neg_respects := by
    intro x y
    exact gaussNeg_respects
  add_comm := gaussAdd_comm
  add_assoc := gaussAdd_assoc
  add_zero := gaussAdd_zero
  zero_add := gaussAdd_zero_left
  add_neg := gaussAdd_neg
  neg_add := gaussAdd_neg_left
  mul_comm := gaussMul_comm
  mul_assoc := gaussMul_assoc
  mul_one := gaussMul_one
  one_mul := gaussMul_one_left
  mul_zero := gaussMul_zero
  zero_mul := gaussMul_zero_left
  left_distrib := gaussMul_add_distrib
  right_distrib := gaussMul_add_distrib_right

end BEDC.Derived.GaussianUp
