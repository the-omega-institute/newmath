import BEDC.Algebra.Rel.IntegerUp

namespace BEDC.Derived.SplitComplexUp

private abbrev Z := BEDC.Algebra.Rel.IntegerUp
private abbrev Zeq := BEDC.Algebra.Rel.IntEq
private abbrev Zzero := BEDC.Algebra.Rel.intZero
private abbrev Zone := BEDC.Algebra.Rel.intOne
private abbrev Zadd := BEDC.Algebra.Rel.IntAdd
private abbrev Zmul := BEDC.Algebra.Rel.IntMul
private abbrev Zneg := BEDC.Algebra.Rel.IntNeg

private def zring : BEDC.Algebra.Rel.RelCommRing Z Zeq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

structure SplitComplex where
  re : Z
  im : Z

def SplitEq (x y : SplitComplex) : Prop :=
  Zeq x.re y.re ∧ Zeq x.im y.im

def splitMk (a b : Z) : SplitComplex :=
  { re := a, im := b }

def splitZero : SplitComplex :=
  splitMk Zzero Zzero

def splitOne : SplitComplex :=
  splitMk Zone Zzero

def splitJ : SplitComplex :=
  splitMk Zzero Zone

def splitAdd (x y : SplitComplex) : SplitComplex :=
  splitMk (Zadd x.re y.re) (Zadd x.im y.im)

def splitNeg (x : SplitComplex) : SplitComplex :=
  splitMk (Zneg x.re) (Zneg x.im)

def splitMul (x y : SplitComplex) : SplitComplex :=
  splitMk
    (Zadd (Zmul x.re y.re) (Zmul x.im y.im))
    (Zadd (Zmul x.re y.im) (Zmul x.im y.re))

def splitConj (x : SplitComplex) : SplitComplex :=
  splitMk x.re (Zneg x.im)

private def zsub (a b : Z) : Z :=
  Zadd a (Zneg b)

def splitNorm (x : SplitComplex) : Z :=
  zsub (Zmul x.re x.re) (Zmul x.im x.im)

def splitOfInt (a : Z) : SplitComplex :=
  splitMk a Zzero

def splitOnePlusJ : SplitComplex :=
  splitMk Zone Zone

def splitOneMinusJ : SplitComplex :=
  splitMk Zone (Zneg Zone)

private theorem zadd_right {a b c : Z} (h : Zeq a b) :
    Zeq (Zadd a c) (Zadd b c) :=
  zring.add_congr h (zring.refl c)

private theorem zadd_left {a b c : Z} (h : Zeq a b) :
    Zeq (Zadd c a) (Zadd c b) :=
  zring.add_congr (zring.refl c) h

private theorem zadd_four_swap (a b c d : Z) :
    Zeq (Zadd (Zadd a b) (Zadd c d))
      (Zadd (Zadd a c) (Zadd b d)) := by
  exact zring.trans (zring.add_assoc a b (Zadd c d))
    (zring.trans
      (zadd_left (a := Zadd b (Zadd c d))
        (b := Zadd (Zadd b c) d)
        (c := a)
        (zring.symm (zring.add_assoc b c d)))
      (zring.trans
        (zadd_left (a := Zadd (Zadd b c) d)
          (b := Zadd (Zadd c b) d)
          (c := a)
          (zadd_right (a := Zadd b c) (b := Zadd c b) (c := d)
            (zring.add_comm b c)))
        (zring.trans
          (zadd_left (a := Zadd (Zadd c b) d)
            (b := Zadd c (Zadd b d))
            (c := a)
            (zring.add_assoc c b d))
          (zring.symm (zring.add_assoc a c (Zadd b d))))))

private theorem zneg_add (a b : Z) :
    Zeq (Zneg (Zadd a b)) (Zadd (Zneg a) (Zneg b)) := by
  have hzero :
      Zeq (Zadd (Zadd a b) (Zadd (Zneg a) (Zneg b))) Zzero := by
    exact zring.trans (zadd_four_swap a b (Zneg a) (Zneg b))
      (zring.trans
        (zring.add_congr (zring.add_neg a) (zring.add_neg b))
        (zring.add_zero Zzero))
  exact zring.symm
    (zring.eq_neg_of_add_eq_zero (a := Zadd a b)
      (b := Zadd (Zneg a) (Zneg b)) hzero)

private theorem zsub_respects {a a' b b' : Z} :
    Zeq a a' -> Zeq b b' -> Zeq (zsub a b) (zsub a' b') := by
  intro ha hb
  exact zring.add_congr ha (zring.neg_congr hb)

private theorem splitMul_assoc_re_expr (a b c d e f : Z) :
    Zeq
      (Zadd (Zmul (Zadd (Zmul a c) (Zmul b d)) e)
        (Zmul (Zadd (Zmul a d) (Zmul b c)) f))
      (Zadd (Zmul a (Zadd (Zmul c e) (Zmul d f)))
        (Zmul b (Zadd (Zmul c f) (Zmul d e)))) := by
  have leftStructured :
      Zeq
        (Zadd (Zmul (Zadd (Zmul a c) (Zmul b d)) e)
          (Zmul (Zadd (Zmul a d) (Zmul b c)) f))
        (Zadd
          (Zadd (Zmul (Zmul a c) e) (Zmul (Zmul b d) e))
          (Zadd (Zmul (Zmul a d) f) (Zmul (Zmul b c) f))) := by
    exact zring.add_congr
      (zring.right_distrib (Zmul a c) (Zmul b d) e)
      (zring.right_distrib (Zmul a d) (Zmul b c) f)
  have rightStructured :
      Zeq
        (Zadd (Zmul a (Zadd (Zmul c e) (Zmul d f)))
          (Zmul b (Zadd (Zmul c f) (Zmul d e))))
        (Zadd
          (Zadd (Zmul (Zmul a c) e) (Zmul (Zmul a d) f))
          (Zadd (Zmul (Zmul b c) f) (Zmul (Zmul b d) e))) := by
    exact zring.add_congr
      (zring.trans (zring.left_distrib a (Zmul c e) (Zmul d f))
        (zring.add_congr
          (zring.symm (zring.mul_assoc a c e))
          (zring.symm (zring.mul_assoc a d f))))
      (zring.trans (zring.left_distrib b (Zmul c f) (Zmul d e))
        (zring.add_congr
          (zring.symm (zring.mul_assoc b c f))
          (zring.symm (zring.mul_assoc b d e))))
  exact zring.trans leftStructured
    (zring.trans
      (zring.trans
        (zadd_four_swap
          (Zmul (Zmul a c) e) (Zmul (Zmul b d) e)
          (Zmul (Zmul a d) f) (Zmul (Zmul b c) f))
        (zadd_left
          (a := Zadd (Zmul (Zmul b d) e) (Zmul (Zmul b c) f))
          (b := Zadd (Zmul (Zmul b c) f) (Zmul (Zmul b d) e))
          (c := Zadd (Zmul (Zmul a c) e) (Zmul (Zmul a d) f))
          (zring.add_comm (Zmul (Zmul b d) e) (Zmul (Zmul b c) f))))
      (zring.symm rightStructured))

private theorem splitMul_assoc_im_expr (a b c d e f : Z) :
    Zeq
      (Zadd (Zmul (Zadd (Zmul a c) (Zmul b d)) f)
        (Zmul (Zadd (Zmul a d) (Zmul b c)) e))
      (Zadd (Zmul a (Zadd (Zmul c f) (Zmul d e)))
        (Zmul b (Zadd (Zmul c e) (Zmul d f)))) := by
  have leftStructured :
      Zeq
        (Zadd (Zmul (Zadd (Zmul a c) (Zmul b d)) f)
          (Zmul (Zadd (Zmul a d) (Zmul b c)) e))
        (Zadd
          (Zadd (Zmul (Zmul a c) f) (Zmul (Zmul b d) f))
          (Zadd (Zmul (Zmul a d) e) (Zmul (Zmul b c) e))) := by
    exact zring.add_congr
      (zring.right_distrib (Zmul a c) (Zmul b d) f)
      (zring.right_distrib (Zmul a d) (Zmul b c) e)
  have rightStructured :
      Zeq
        (Zadd (Zmul a (Zadd (Zmul c f) (Zmul d e)))
          (Zmul b (Zadd (Zmul c e) (Zmul d f))))
        (Zadd
          (Zadd (Zmul (Zmul a c) f) (Zmul (Zmul a d) e))
          (Zadd (Zmul (Zmul b c) e) (Zmul (Zmul b d) f))) := by
    exact zring.add_congr
      (zring.trans (zring.left_distrib a (Zmul c f) (Zmul d e))
        (zring.add_congr
          (zring.symm (zring.mul_assoc a c f))
          (zring.symm (zring.mul_assoc a d e))))
      (zring.trans (zring.left_distrib b (Zmul c e) (Zmul d f))
        (zring.add_congr
          (zring.symm (zring.mul_assoc b c e))
          (zring.symm (zring.mul_assoc b d f))))
  exact zring.trans leftStructured
    (zring.trans
      (zring.trans
        (zadd_four_swap
          (Zmul (Zmul a c) f) (Zmul (Zmul b d) f)
          (Zmul (Zmul a d) e) (Zmul (Zmul b c) e))
        (zadd_left
          (a := Zadd (Zmul (Zmul b d) f) (Zmul (Zmul b c) e))
          (b := Zadd (Zmul (Zmul b c) e) (Zmul (Zmul b d) f))
          (c := Zadd (Zmul (Zmul a c) f) (Zmul (Zmul a d) e))
          (zring.add_comm (Zmul (Zmul b d) f) (Zmul (Zmul b c) e))))
      (zring.symm rightStructured))

private theorem splitMul_add_distrib_re_expr (a b c d e f : Z) :
    Zeq
      (Zadd (Zmul a (Zadd c e)) (Zmul b (Zadd d f)))
      (Zadd (Zadd (Zmul a c) (Zmul b d))
        (Zadd (Zmul a e) (Zmul b f))) := by
  exact zring.trans
    (zring.add_congr
      (zring.left_distrib a c e)
      (zring.left_distrib b d f))
    (zadd_four_swap (Zmul a c) (Zmul a e) (Zmul b d) (Zmul b f))

private theorem splitMul_add_distrib_im_expr (a b c d e f : Z) :
    Zeq
      (Zadd (Zmul a (Zadd d f)) (Zmul b (Zadd c e)))
      (Zadd (Zadd (Zmul a d) (Zmul b c))
        (Zadd (Zmul a f) (Zmul b e))) := by
  exact zring.trans
    (zring.add_congr
      (zring.left_distrib a d f)
      (zring.left_distrib b c e))
    (zadd_four_swap (Zmul a d) (Zmul a f) (Zmul b c) (Zmul b e))

theorem SplitEq_refl (x : SplitComplex) :
    SplitEq x x := by
  constructor
  · exact zring.refl x.re
  · exact zring.refl x.im

theorem SplitEq_symm {x y : SplitComplex} :
    SplitEq x y -> SplitEq y x := by
  intro h
  constructor
  · exact zring.symm h.left
  · exact zring.symm h.right

theorem SplitEq_trans {x y z : SplitComplex} :
    SplitEq x y -> SplitEq y z -> SplitEq x z := by
  intro xy yz
  constructor
  · exact zring.trans xy.left yz.left
  · exact zring.trans xy.right yz.right

theorem splitAdd_respects {x x' y y' : SplitComplex} :
    SplitEq x x' -> SplitEq y y' ->
      SplitEq (splitAdd x y) (splitAdd x' y') := by
  intro hx hy
  constructor
  · exact zring.add_congr hx.left hy.left
  · exact zring.add_congr hx.right hy.right

theorem splitNeg_respects {x y : SplitComplex} :
    SplitEq x y -> SplitEq (splitNeg x) (splitNeg y) := by
  intro h
  constructor
  · exact zring.neg_congr h.left
  · exact zring.neg_congr h.right

theorem splitMul_respects {x x' y y' : SplitComplex} :
    SplitEq x x' -> SplitEq y y' ->
      SplitEq (splitMul x y) (splitMul x' y') := by
  intro hx hy
  constructor
  · exact zring.add_congr
      (zring.mul_congr hx.left hy.left)
      (zring.mul_congr hx.right hy.right)
  · exact zring.add_congr
      (zring.mul_congr hx.left hy.right)
      (zring.mul_congr hx.right hy.left)

theorem splitAdd_comm (x y : SplitComplex) :
    SplitEq (splitAdd x y) (splitAdd y x) := by
  constructor
  · exact zring.add_comm x.re y.re
  · exact zring.add_comm x.im y.im

theorem splitAdd_assoc (x y z : SplitComplex) :
    SplitEq (splitAdd (splitAdd x y) z) (splitAdd x (splitAdd y z)) := by
  constructor
  · exact zring.add_assoc x.re y.re z.re
  · exact zring.add_assoc x.im y.im z.im

theorem splitAdd_zero (x : SplitComplex) :
    SplitEq (splitAdd x splitZero) x := by
  constructor
  · exact zring.add_zero x.re
  · exact zring.add_zero x.im

theorem splitZero_add (x : SplitComplex) :
    SplitEq (splitAdd splitZero x) x := by
  constructor
  · exact zring.zero_add x.re
  · exact zring.zero_add x.im

theorem splitAdd_neg (x : SplitComplex) :
    SplitEq (splitAdd x (splitNeg x)) splitZero := by
  constructor
  · exact zring.add_neg x.re
  · exact zring.add_neg x.im

theorem splitNeg_add (x : SplitComplex) :
    SplitEq (splitAdd (splitNeg x) x) splitZero := by
  constructor
  · exact zring.neg_add x.re
  · exact zring.neg_add x.im

theorem splitMul_comm (x y : SplitComplex) :
    SplitEq (splitMul x y) (splitMul y x) := by
  constructor
  · exact zring.add_congr
      (zring.mul_comm x.re y.re)
      (zring.mul_comm x.im y.im)
  · exact zring.trans
      (zring.add_congr
        (zring.mul_comm x.re y.im)
        (zring.mul_comm x.im y.re))
      (zring.add_comm (Zmul y.im x.re) (Zmul y.re x.im))

theorem splitMul_assoc (x y z : SplitComplex) :
    SplitEq (splitMul (splitMul x y) z) (splitMul x (splitMul y z)) := by
  constructor
  · exact splitMul_assoc_re_expr x.re x.im y.re y.im z.re z.im
  · exact splitMul_assoc_im_expr x.re x.im y.re y.im z.re z.im

theorem splitMul_one (x : SplitComplex) :
    SplitEq (splitMul x splitOne) x := by
  constructor
  · exact zring.trans
      (zring.add_congr
        (zring.mul_one x.re)
        (zring.mul_zero x.im))
      (zring.add_zero x.re)
  · exact zring.trans
      (zring.add_congr
        (zring.mul_zero x.re)
        (zring.mul_one x.im))
      (zring.zero_add x.im)

theorem splitOne_mul (x : SplitComplex) :
    SplitEq (splitMul splitOne x) x := by
  constructor
  · exact zring.trans
      (zring.add_congr
        (zring.one_mul x.re)
        (zring.zero_mul x.im))
      (zring.add_zero x.re)
  · exact zring.trans
      (zring.add_congr
        (zring.one_mul x.im)
        (zring.zero_mul x.re))
      (zring.add_zero x.im)

theorem splitMul_zero (x : SplitComplex) :
    SplitEq (splitMul x splitZero) splitZero := by
  constructor
  · exact zring.trans
      (zring.add_congr
        (zring.mul_zero x.re)
        (zring.mul_zero x.im))
      (zring.add_zero Zzero)
  · exact zring.trans
      (zring.add_congr
        (zring.mul_zero x.re)
        (zring.mul_zero x.im))
      (zring.add_zero Zzero)

theorem splitZero_mul (x : SplitComplex) :
    SplitEq (splitMul splitZero x) splitZero := by
  constructor
  · exact zring.trans
      (zring.add_congr
        (zring.zero_mul x.re)
        (zring.zero_mul x.im))
      (zring.add_zero Zzero)
  · exact zring.trans
      (zring.add_congr
        (zring.zero_mul x.im)
        (zring.zero_mul x.re))
      (zring.add_zero Zzero)

theorem splitMul_add_distrib (x y z : SplitComplex) :
    SplitEq (splitMul x (splitAdd y z))
      (splitAdd (splitMul x y) (splitMul x z)) := by
  constructor
  · exact splitMul_add_distrib_re_expr x.re x.im y.re y.im z.re z.im
  · exact splitMul_add_distrib_im_expr x.re x.im y.re y.im z.re z.im

theorem splitMul_add_distrib_right (x y z : SplitComplex) :
    SplitEq (splitMul (splitAdd x y) z)
      (splitAdd (splitMul x z) (splitMul y z)) := by
  exact SplitEq_trans (splitMul_comm (splitAdd x y) z)
    (SplitEq_trans (splitMul_add_distrib z x y)
      (splitAdd_respects (splitMul_comm z x) (splitMul_comm z y)))

theorem splitMul_coefficients (a b c d : Z) :
    SplitEq (splitMul (splitMk a b) (splitMk c d))
      (splitMk (Zadd (Zmul a c) (Zmul b d))
        (Zadd (Zmul a d) (Zmul b c))) := by
  constructor
  · exact zring.refl (Zadd (Zmul a c) (Zmul b d))
  · exact zring.refl (Zadd (Zmul a d) (Zmul b c))

theorem splitJ_mul_self :
    SplitEq (splitMul splitJ splitJ) splitOne := by
  constructor
  · exact zring.trans
      (zring.add_congr
        (zring.zero_mul Zzero)
        (zring.mul_one Zone))
      (zring.zero_add Zone)
  · exact zring.trans
      (zring.add_congr
        (zring.zero_mul Zone)
        (zring.mul_zero Zone))
      (zring.add_zero Zzero)

theorem splitConj_respects {x y : SplitComplex} :
    SplitEq x y -> SplitEq (splitConj x) (splitConj y) := by
  intro h
  constructor
  · exact h.left
  · exact zring.neg_congr h.right

theorem splitConj_involutive (x : SplitComplex) :
    SplitEq (splitConj (splitConj x)) x := by
  constructor
  · exact zring.refl x.re
  · exact zring.neg_neg x.im

theorem splitConj_mul (x y : SplitComplex) :
    SplitEq (splitConj (splitMul x y))
      (splitMul (splitConj x) (splitConj y)) := by
  constructor
  · exact zring.add_congr
      (zring.refl (Zmul x.re y.re))
      (zring.symm (zring.neg_neg_mul_neg x.im y.im))
  · exact zring.trans (zneg_add (Zmul x.re y.im) (Zmul x.im y.re))
      (zring.add_congr
        (zring.symm (zring.mul_neg x.re y.im))
        (zring.symm (zring.neg_mul x.im y.re)))

theorem splitMul_conj_norm (x : SplitComplex) :
    SplitEq (splitMul x (splitConj x)) (splitOfInt (splitNorm x)) := by
  constructor
  · exact zring.add_congr
      (zring.refl (Zmul x.re x.re))
      (zring.mul_neg x.im x.im)
  · exact zring.trans
      (zring.add_congr
        (zring.mul_neg x.re x.im)
        (zring.refl (Zmul x.im x.re)))
      (zring.trans
        (zadd_right
          (a := Zneg (Zmul x.re x.im))
          (b := Zneg (Zmul x.im x.re))
          (c := Zmul x.im x.re)
          (zring.neg_congr (zring.mul_comm x.re x.im)))
        (zring.neg_add (Zmul x.im x.re)))

theorem splitConj_mul_self_norm (x : SplitComplex) :
    SplitEq (splitMul (splitConj x) x) (splitOfInt (splitNorm x)) :=
  SplitEq_trans (splitMul_comm (splitConj x) x) (splitMul_conj_norm x)

theorem splitOfInt_mul (a b : Z) :
    SplitEq (splitMul (splitOfInt a) (splitOfInt b)) (splitOfInt (Zmul a b)) := by
  constructor
  · exact zring.trans
      (zring.add_congr
        (zring.refl (Zmul a b))
        (zring.mul_zero Zzero))
      (zring.add_zero (Zmul a b))
  · exact zring.trans
      (zring.add_congr
        (zring.mul_zero a)
        (zring.zero_mul b))
      (zring.add_zero Zzero)

theorem splitNorm_respects {x y : SplitComplex} :
    SplitEq x y -> Zeq (splitNorm x) (splitNorm y) := by
  intro h
  exact zsub_respects
    (zring.mul_congr h.left h.left)
    (zring.mul_congr h.right h.right)

theorem splitNorm_mul (x y : SplitComplex) :
    Zeq (splitNorm (splitMul x y))
      (Zmul (splitNorm x) (splitNorm y)) := by
  let p := splitMul x y
  have productNorm :
      SplitEq (splitMul p (splitConj p)) (splitOfInt (splitNorm p)) :=
    splitMul_conj_norm p
  have conjProduct :
      SplitEq (splitConj p) (splitMul (splitConj x) (splitConj y)) := by
    exact splitConj_mul x y
  have replaceConj :
      SplitEq (splitMul p (splitConj p))
        (splitMul (splitMul x y)
          (splitMul (splitConj x) (splitConj y))) := by
    exact splitMul_respects (SplitEq_refl p) conjProduct
  have reassocLeft :
      SplitEq (splitMul (splitMul x y)
          (splitMul (splitConj x) (splitConj y)))
        (splitMul x
          (splitMul y (splitMul (splitConj x) (splitConj y)))) :=
    splitMul_assoc x y (splitMul (splitConj x) (splitConj y))
  have moveConjX :
      SplitEq
        (splitMul y (splitMul (splitConj x) (splitConj y)))
        (splitMul (splitConj x) (splitMul y (splitConj y))) := by
    exact SplitEq_trans
      (SplitEq_symm (splitMul_assoc y (splitConj x) (splitConj y)))
      (SplitEq_trans
        (splitMul_respects (splitMul_comm y (splitConj x))
          (SplitEq_refl (splitConj y)))
        (splitMul_assoc (splitConj x) y (splitConj y)))
  have reassocRight :
      SplitEq
        (splitMul x
          (splitMul (splitConj x) (splitMul y (splitConj y))))
        (splitMul (splitMul x (splitConj x))
          (splitMul y (splitConj y))) :=
    SplitEq_symm (splitMul_assoc x (splitConj x)
      (splitMul y (splitConj y)))
  have toNormFactors :
      SplitEq
        (splitMul (splitMul x y)
          (splitMul (splitConj x) (splitConj y)))
        (splitMul (splitOfInt (splitNorm x)) (splitOfInt (splitNorm y))) := by
    exact SplitEq_trans reassocLeft
      (SplitEq_trans (splitMul_respects (SplitEq_refl x) moveConjX)
        (SplitEq_trans reassocRight
          (splitMul_respects (splitMul_conj_norm x)
            (splitMul_conj_norm y))))
  have productAsNorm :
      SplitEq (splitOfInt (splitNorm p))
        (splitMul (splitOfInt (splitNorm x)) (splitOfInt (splitNorm y))) :=
    SplitEq_trans (SplitEq_symm productNorm)
      (SplitEq_trans replaceConj toNormFactors)
  have productAsInt :
      SplitEq (splitMul (splitOfInt (splitNorm x)) (splitOfInt (splitNorm y)))
        (splitOfInt (Zmul (splitNorm x) (splitNorm y))) :=
    splitOfInt_mul (splitNorm x) (splitNorm y)
  exact zring.trans productAsNorm.left productAsInt.left

theorem splitOnePlusJ_mul_oneMinusJ_zero :
    SplitEq (splitMul splitOnePlusJ splitOneMinusJ) splitZero := by
  have negOneMul :
      Zeq (Zmul Zone (Zneg Zone)) (Zneg Zone) :=
    zring.trans (zring.mul_neg Zone Zone)
      (zring.neg_congr (zring.mul_one Zone))
  constructor
  · exact zring.trans
      (zring.add_congr
        (zring.mul_one Zone)
        negOneMul)
      (zring.add_neg Zone)
  · exact zring.trans
      (zring.add_congr
        negOneMul
        (zring.mul_one Zone))
      (zring.neg_add Zone)

structure SplitComplexCommRingLaws where
  eq_refl : ∀ x : SplitComplex, SplitEq x x
  eq_symm : ∀ {x y : SplitComplex}, SplitEq x y -> SplitEq y x
  eq_trans :
    ∀ {x y z : SplitComplex}, SplitEq x y -> SplitEq y z -> SplitEq x z
  add_respects :
    ∀ {x x' y y' : SplitComplex}, SplitEq x x' -> SplitEq y y' ->
      SplitEq (splitAdd x y) (splitAdd x' y')
  mul_respects :
    ∀ {x x' y y' : SplitComplex}, SplitEq x x' -> SplitEq y y' ->
      SplitEq (splitMul x y) (splitMul x' y')
  neg_respects :
    ∀ {x y : SplitComplex}, SplitEq x y -> SplitEq (splitNeg x) (splitNeg y)
  add_comm : ∀ x y : SplitComplex, SplitEq (splitAdd x y) (splitAdd y x)
  add_assoc :
    ∀ x y z : SplitComplex,
      SplitEq (splitAdd (splitAdd x y) z) (splitAdd x (splitAdd y z))
  add_zero : ∀ x : SplitComplex, SplitEq (splitAdd x splitZero) x
  zero_add : ∀ x : SplitComplex, SplitEq (splitAdd splitZero x) x
  add_neg : ∀ x : SplitComplex, SplitEq (splitAdd x (splitNeg x)) splitZero
  neg_add : ∀ x : SplitComplex, SplitEq (splitAdd (splitNeg x) x) splitZero
  mul_comm : ∀ x y : SplitComplex, SplitEq (splitMul x y) (splitMul y x)
  mul_assoc :
    ∀ x y z : SplitComplex,
      SplitEq (splitMul (splitMul x y) z) (splitMul x (splitMul y z))
  mul_one : ∀ x : SplitComplex, SplitEq (splitMul x splitOne) x
  one_mul : ∀ x : SplitComplex, SplitEq (splitMul splitOne x) x
  mul_zero : ∀ x : SplitComplex, SplitEq (splitMul x splitZero) splitZero
  zero_mul : ∀ x : SplitComplex, SplitEq (splitMul splitZero x) splitZero
  left_distrib :
    ∀ x y z : SplitComplex,
      SplitEq (splitMul x (splitAdd y z))
        (splitAdd (splitMul x y) (splitMul x z))
  right_distrib :
    ∀ x y z : SplitComplex,
      SplitEq (splitMul (splitAdd x y) z)
        (splitAdd (splitMul x z) (splitMul y z))

def SplitComplex_comm_ring_laws : SplitComplexCommRingLaws where
  eq_refl := SplitEq_refl
  eq_symm := by
    intro x y
    exact SplitEq_symm
  eq_trans := by
    intro x y z
    exact SplitEq_trans
  add_respects := by
    intro x x' y y'
    exact splitAdd_respects
  mul_respects := by
    intro x x' y y'
    exact splitMul_respects
  neg_respects := by
    intro x y
    exact splitNeg_respects
  add_comm := splitAdd_comm
  add_assoc := splitAdd_assoc
  add_zero := splitAdd_zero
  zero_add := splitZero_add
  add_neg := splitAdd_neg
  neg_add := splitNeg_add
  mul_comm := splitMul_comm
  mul_assoc := splitMul_assoc
  mul_one := splitMul_one
  one_mul := splitOne_mul
  mul_zero := splitMul_zero
  zero_mul := splitZero_mul
  left_distrib := splitMul_add_distrib
  right_distrib := splitMul_add_distrib_right

instance SplitComplex_RelEquiv :
    BEDC.Algebra.Rel.RelEquiv SplitComplex where
  rel := SplitEq
  refl := SplitEq_refl
  symm := by
    intro x y
    exact SplitEq_symm
  trans := by
    intro x y z
    exact SplitEq_trans

instance SplitComplex_RelCommRing :
    BEDC.Algebra.Rel.RelCommRing SplitComplex SplitEq where
  zero := splitZero
  one := splitOne
  add := splitAdd
  mul := splitMul
  neg := splitNeg
  refl := SplitComplex_comm_ring_laws.eq_refl
  symm := by
    intro x y
    exact SplitComplex_comm_ring_laws.eq_symm
  trans := by
    intro x y z
    exact SplitComplex_comm_ring_laws.eq_trans
  add_congr := by
    intro x x' y y'
    exact SplitComplex_comm_ring_laws.add_respects
  mul_congr := by
    intro x x' y y'
    exact SplitComplex_comm_ring_laws.mul_respects
  neg_congr := by
    intro x y
    exact SplitComplex_comm_ring_laws.neg_respects
  add_assoc := SplitComplex_comm_ring_laws.add_assoc
  add_comm := SplitComplex_comm_ring_laws.add_comm
  add_zero := SplitComplex_comm_ring_laws.add_zero
  zero_add := SplitComplex_comm_ring_laws.zero_add
  add_neg := SplitComplex_comm_ring_laws.add_neg
  neg_add := SplitComplex_comm_ring_laws.neg_add
  mul_assoc := SplitComplex_comm_ring_laws.mul_assoc
  mul_comm := SplitComplex_comm_ring_laws.mul_comm
  mul_one := SplitComplex_comm_ring_laws.mul_one
  one_mul := SplitComplex_comm_ring_laws.one_mul
  mul_zero := SplitComplex_comm_ring_laws.mul_zero
  zero_mul := SplitComplex_comm_ring_laws.zero_mul
  left_distrib := SplitComplex_comm_ring_laws.left_distrib
  right_distrib := SplitComplex_comm_ring_laws.right_distrib

theorem splitNeg_mul (x y : SplitComplex) :
    SplitEq (splitMul (splitNeg x) y) (splitNeg (splitMul x y)) :=
  SplitComplex_RelCommRing.neg_mul x y

theorem splitMul_neg (x y : SplitComplex) :
    SplitEq (splitMul x (splitNeg y)) (splitNeg (splitMul x y)) :=
  SplitComplex_RelCommRing.mul_neg x y

theorem splitNeg_neg (x : SplitComplex) :
    SplitEq (splitNeg (splitNeg x)) x :=
  SplitComplex_RelCommRing.neg_neg x

end BEDC.Derived.SplitComplexUp
