import BEDC.Algebra.Rel.IntegerUp

namespace BEDC.Derived.PellUp

abbrev Z := BEDC.Algebra.Rel.IntegerUp
abbrev Zeq := BEDC.Algebra.Rel.IntEq
abbrev Zzero := BEDC.Algebra.Rel.intZero
abbrev Zone := BEDC.Algebra.Rel.intOne
abbrev Zadd := BEDC.Algebra.Rel.IntAdd
abbrev Zmul := BEDC.Algebra.Rel.IntMul
abbrev Zneg := BEDC.Algebra.Rel.IntNeg

private def R : BEDC.Algebra.Rel.RelCommRing Z Zeq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

private theorem zadd_right {a b c : Z} (h : Zeq a b) :
    Zeq (Zadd a c) (Zadd b c) :=
  R.add_congr h (R.refl c)

private theorem zadd_left {a b c : Z} (h : Zeq a b) :
    Zeq (Zadd c a) (Zadd c b) :=
  R.add_congr (R.refl c) h

private theorem zmul_right {a b c : Z} (h : Zeq a b) :
    Zeq (Zmul a c) (Zmul b c) :=
  R.mul_congr h (R.refl c)

private theorem zmul_left {a b c : Z} (h : Zeq a b) :
    Zeq (Zmul c a) (Zmul c b) :=
  R.mul_congr (R.refl c) h

def zsub (a b : Z) : Z :=
  Zadd a (Zneg b)

def zsq (a : Z) : Z :=
  Zmul a a

private theorem z_eq_neg_of_add_eq_zero {a b : Z} :
    Zeq (Zadd a b) Zzero -> Zeq b (Zneg a) := by
  intro h
  exact R.trans (R.symm (R.zero_add b))
    (R.trans (zadd_right (a := Zzero) (b := Zadd (Zneg a) a) (c := b)
        (R.symm (R.neg_add a)))
      (R.trans (R.add_assoc (Zneg a) a b)
        (R.trans (zadd_left (a := Zadd a b) (b := Zzero) (c := Zneg a) h)
          (R.add_zero (Zneg a)))))

private theorem zneg_zero :
    Zeq (Zneg Zzero) Zzero :=
  R.trans (R.symm (R.zero_add (Zneg Zzero))) (R.neg_add Zzero)

private theorem zneg_neg (a : Z) :
    Zeq (Zneg (Zneg a)) a :=
  R.symm (z_eq_neg_of_add_eq_zero (a := Zneg a) (b := a) (R.neg_add a))

private theorem zadd_four_swap (a b c d : Z) :
    Zeq (Zadd (Zadd a b) (Zadd c d))
      (Zadd (Zadd a c) (Zadd b d)) := by
  exact R.trans (R.add_assoc a b (Zadd c d))
    (R.trans
      (zadd_left (a := Zadd b (Zadd c d))
        (b := Zadd (Zadd b c) d)
        (c := a)
        (R.symm (R.add_assoc b c d)))
      (R.trans
        (zadd_left (a := Zadd (Zadd b c) d)
          (b := Zadd (Zadd c b) d)
          (c := a)
          (zadd_right (a := Zadd b c) (b := Zadd c b) (c := d)
            (R.add_comm b c)))
        (R.trans
          (zadd_left (a := Zadd (Zadd c b) d)
            (b := Zadd c (Zadd b d))
            (c := a)
            (R.add_assoc c b d))
          (R.symm (R.add_assoc a c (Zadd b d))))))

private theorem zneg_add (a b : Z) :
    Zeq (Zneg (Zadd a b)) (Zadd (Zneg a) (Zneg b)) := by
  have hzero :
      Zeq (Zadd (Zadd a b) (Zadd (Zneg a) (Zneg b))) Zzero := by
    exact R.trans (zadd_four_swap a b (Zneg a) (Zneg b))
      (R.trans
        (R.add_congr (R.add_neg a) (R.add_neg b))
        (R.add_zero Zzero))
  exact R.symm
    (z_eq_neg_of_add_eq_zero (a := Zadd a b)
      (b := Zadd (Zneg a) (Zneg b)) hzero)

private theorem zmul_neg_right (a b : Z) :
    Zeq (Zmul a (Zneg b)) (Zneg (Zmul a b)) := by
  have hzero :
      Zeq (Zadd (Zmul a b) (Zmul a (Zneg b))) Zzero := by
    exact R.trans (R.symm (R.left_distrib a b (Zneg b)))
      (R.trans (zmul_left (a := Zadd b (Zneg b)) (b := Zzero) (c := a)
          (R.add_neg b))
        (R.mul_zero a))
  exact z_eq_neg_of_add_eq_zero (a := Zmul a b) (b := Zmul a (Zneg b)) hzero

private theorem zmul_neg_left (a b : Z) :
    Zeq (Zmul (Zneg a) b) (Zneg (Zmul a b)) := by
  have hzero :
      Zeq (Zadd (Zmul a b) (Zmul (Zneg a) b)) Zzero := by
    exact R.trans (R.symm (R.right_distrib a (Zneg a) b))
      (R.trans (zmul_right (a := Zadd a (Zneg a)) (b := Zzero) (c := b)
          (R.add_neg a))
        (R.zero_mul b))
  exact z_eq_neg_of_add_eq_zero (a := Zmul a b) (b := Zmul (Zneg a) b) hzero

private theorem zmul_neg_neg (a b : Z) :
    Zeq (Zmul (Zneg a) (Zneg b)) (Zmul a b) := by
  exact R.trans (zmul_neg_left a (Zneg b))
    (R.trans (R.neg_congr (zmul_neg_right a b))
      (zneg_neg (Zmul a b)))

private theorem zsq_neg (a : Z) :
    Zeq (zsq (Zneg a)) (zsq a) :=
  zmul_neg_neg a a

private theorem zsub_respects {a a' b b' : Z} :
    Zeq a a' -> Zeq b b' -> Zeq (zsub a b) (zsub a' b') := by
  intro ha hb
  exact R.add_congr ha (R.neg_congr hb)

private theorem zmul_nested_swap (a b c : Z) :
    Zeq (Zmul a (Zmul b c)) (Zmul b (Zmul a c)) := by
  exact R.trans (R.symm (R.mul_assoc a b c))
    (R.trans (zmul_right (a := Zmul a b) (b := Zmul b a) (c := c)
        (R.mul_comm a b))
      (R.mul_assoc b a c))

private theorem zmul_assoc_inside (a b c d : Z) :
    Zeq (Zmul (Zmul a (Zmul b c)) d)
      (Zmul a (Zmul b (Zmul c d))) := by
  exact R.trans (R.mul_assoc a (Zmul b c) d)
    (zmul_left (a := Zmul (Zmul b c) d)
      (b := Zmul b (Zmul c d))
      (c := a)
      (R.mul_assoc b c d))

private theorem zmul_left_assoc_inside (a b c d : Z) :
    Zeq (Zmul a (Zmul (Zmul b c) d))
      (Zmul a (Zmul b (Zmul c d))) :=
  zmul_left (a := Zmul (Zmul b c) d)
    (b := Zmul b (Zmul c d))
    (c := a)
    (R.mul_assoc b c d)

private theorem zmul_left_nested_swap (a b c d : Z) :
    Zeq (Zmul a (Zmul b (Zmul c d)))
      (Zmul b (Zmul a (Zmul c d))) :=
  zmul_nested_swap a b (Zmul c d)

structure PellPair where
  x : Z
  y : Z

def PellPairEq (a b : PellPair) : Prop :=
  Zeq a.x b.x ∧ Zeq a.y b.y

def pellPairOne : PellPair :=
  { x := Zone, y := Zzero }

def pellPairMul (D : Z) (a b : PellPair) : PellPair :=
  { x := Zadd (Zmul a.x b.x) (Zmul D (Zmul a.y b.y)),
    y := Zadd (Zmul a.x b.y) (Zmul a.y b.x) }

def pellPairInv (a : PellPair) : PellPair :=
  { x := a.x, y := Zneg a.y }

def pellPairOfInt (a : Z) : PellPair :=
  { x := a, y := Zzero }

def pellNorm (D : Z) (x y : Z) : Z :=
  zsub (zsq x) (Zmul D (zsq y))

def IsPellSolution (D : Z) (x y : Z) : Prop :=
  Zeq (pellNorm D x y) Zone

def pellComposeX (D x1 y1 x2 y2 : Z) : Z :=
  Zadd (Zmul x1 x2) (Zmul D (Zmul y1 y2))

def pellComposeY (_D x1 y1 x2 y2 : Z) : Z :=
  Zadd (Zmul x1 y2) (Zmul y1 x2)

def pellSolutionStep (D a b : Z) (p : PellPair) : PellPair :=
  pellPairMul D { x := a, y := b } p

def pellSolutionPow (D a b : Z) : Nat -> PellPair
  | Nat.zero => pellPairOne
  | Nat.succ n => pellSolutionStep D a b (pellSolutionPow D a b n)

theorem PellPairEq_refl (a : PellPair) :
    PellPairEq a a := by
  constructor
  · exact R.refl a.x
  · exact R.refl a.y

theorem PellPairEq_symm {a b : PellPair} :
    PellPairEq a b -> PellPairEq b a := by
  intro h
  constructor
  · exact R.symm h.left
  · exact R.symm h.right

theorem PellPairEq_trans {a b c : PellPair} :
    PellPairEq a b -> PellPairEq b c -> PellPairEq a c := by
  intro ab bc
  constructor
  · exact R.trans ab.left bc.left
  · exact R.trans ab.right bc.right

theorem pellPairMul_respects {D : Z} {a a' b b' : PellPair} :
    PellPairEq a a' -> PellPairEq b b' ->
      PellPairEq (pellPairMul D a b) (pellPairMul D a' b') := by
  intro ha hb
  constructor
  · exact R.add_congr
      (R.mul_congr ha.left hb.left)
      (zmul_left (a := Zmul a.y b.y) (b := Zmul a'.y b'.y) (c := D)
        (R.mul_congr ha.right hb.right))
  · exact R.add_congr
      (R.mul_congr ha.left hb.right)
      (R.mul_congr ha.right hb.left)

theorem pellPairMul_comm (D : Z) (a b : PellPair) :
    PellPairEq (pellPairMul D a b) (pellPairMul D b a) := by
  constructor
  · exact R.add_congr
      (R.mul_comm a.x b.x)
      (zmul_left (a := Zmul a.y b.y) (b := Zmul b.y a.y) (c := D)
        (R.mul_comm a.y b.y))
  · exact R.trans
      (R.add_congr (R.mul_comm a.x b.y) (R.mul_comm a.y b.x))
      (R.add_comm (Zmul b.y a.x) (Zmul b.x a.y))

private theorem pellPairMul_assoc_x_expr (D a b c d e f : Z) :
    Zeq
      (Zadd
        (Zmul (Zadd (Zmul a c) (Zmul D (Zmul b d))) e)
        (Zmul D (Zmul (Zadd (Zmul a d) (Zmul b c)) f)))
      (Zadd
        (Zmul a (Zadd (Zmul c e) (Zmul D (Zmul d f))))
        (Zmul D (Zmul b (Zadd (Zmul c f) (Zmul d e))))) := by
  let ACE := Zmul a (Zmul c e)
  let DBDE := Zmul D (Zmul b (Zmul d e))
  let DADF := Zmul D (Zmul a (Zmul d f))
  let DBCF := Zmul D (Zmul b (Zmul c f))
  have leftStructured :
      Zeq
        (Zadd
          (Zmul (Zadd (Zmul a c) (Zmul D (Zmul b d))) e)
          (Zmul D (Zmul (Zadd (Zmul a d) (Zmul b c)) f)))
        (Zadd (Zadd ACE DBDE) (Zadd DADF DBCF)) := by
    have first :
        Zeq (Zmul (Zadd (Zmul a c) (Zmul D (Zmul b d))) e)
          (Zadd ACE DBDE) := by
      exact R.trans (R.right_distrib (Zmul a c) (Zmul D (Zmul b d)) e)
        (R.add_congr
          (R.mul_assoc a c e)
          (zmul_assoc_inside D b d e))
    have second :
        Zeq (Zmul D (Zmul (Zadd (Zmul a d) (Zmul b c)) f))
          (Zadd DADF DBCF) := by
      exact R.trans
        (zmul_left (a := Zmul (Zadd (Zmul a d) (Zmul b c)) f)
          (b := Zadd (Zmul (Zmul a d) f) (Zmul (Zmul b c) f))
          (c := D)
          (R.right_distrib (Zmul a d) (Zmul b c) f))
        (R.trans (R.left_distrib D (Zmul (Zmul a d) f) (Zmul (Zmul b c) f))
          (R.add_congr
            (zmul_left_assoc_inside D a d f)
            (zmul_left_assoc_inside D b c f)))
    exact R.add_congr first second
  have rightStructured :
      Zeq
        (Zadd
          (Zmul a (Zadd (Zmul c e) (Zmul D (Zmul d f))))
          (Zmul D (Zmul b (Zadd (Zmul c f) (Zmul d e)))))
        (Zadd (Zadd ACE DADF) (Zadd DBCF DBDE)) := by
    have first :
        Zeq (Zmul a (Zadd (Zmul c e) (Zmul D (Zmul d f))))
          (Zadd ACE DADF) := by
      exact R.trans (R.left_distrib a (Zmul c e) (Zmul D (Zmul d f)))
        (R.add_congr
          (R.refl ACE)
          (zmul_left_nested_swap a D d f))
    have second :
        Zeq (Zmul D (Zmul b (Zadd (Zmul c f) (Zmul d e))))
          (Zadd DBCF DBDE) := by
      exact R.trans
        (zmul_left (a := Zmul b (Zadd (Zmul c f) (Zmul d e)))
          (b := Zadd (Zmul b (Zmul c f)) (Zmul b (Zmul d e)))
          (c := D)
          (R.left_distrib b (Zmul c f) (Zmul d e)))
        (R.left_distrib D (Zmul b (Zmul c f)) (Zmul b (Zmul d e)))
    exact R.add_congr first second
  have permuted :
      Zeq (Zadd (Zadd ACE DBDE) (Zadd DADF DBCF))
        (Zadd (Zadd ACE DADF) (Zadd DBCF DBDE)) := by
    exact R.trans (zadd_four_swap ACE DBDE DADF DBCF)
      (zadd_left (a := Zadd DBDE DBCF) (b := Zadd DBCF DBDE)
        (c := Zadd ACE DADF)
        (R.add_comm DBDE DBCF))
  exact R.trans leftStructured (R.trans permuted (R.symm rightStructured))

private theorem pellPairMul_assoc_y_expr (D a b c d e f : Z) :
    Zeq
      (Zadd
        (Zmul (Zadd (Zmul a c) (Zmul D (Zmul b d))) f)
        (Zmul (Zadd (Zmul a d) (Zmul b c)) e))
      (Zadd
        (Zmul a (Zadd (Zmul c f) (Zmul d e)))
        (Zmul b (Zadd (Zmul c e) (Zmul D (Zmul d f))))) := by
  let ACF := Zmul a (Zmul c f)
  let DBDF := Zmul D (Zmul b (Zmul d f))
  let ADE := Zmul a (Zmul d e)
  let BCE := Zmul b (Zmul c e)
  have leftStructured :
      Zeq
        (Zadd
          (Zmul (Zadd (Zmul a c) (Zmul D (Zmul b d))) f)
          (Zmul (Zadd (Zmul a d) (Zmul b c)) e))
        (Zadd (Zadd ACF DBDF) (Zadd ADE BCE)) := by
    have first :
        Zeq (Zmul (Zadd (Zmul a c) (Zmul D (Zmul b d))) f)
          (Zadd ACF DBDF) := by
      exact R.trans (R.right_distrib (Zmul a c) (Zmul D (Zmul b d)) f)
        (R.add_congr
          (R.mul_assoc a c f)
          (zmul_assoc_inside D b d f))
    have second :
        Zeq (Zmul (Zadd (Zmul a d) (Zmul b c)) e)
          (Zadd ADE BCE) := by
      exact R.trans (R.right_distrib (Zmul a d) (Zmul b c) e)
        (R.add_congr (R.mul_assoc a d e) (R.mul_assoc b c e))
    exact R.add_congr first second
  have rightStructured :
      Zeq
        (Zadd
          (Zmul a (Zadd (Zmul c f) (Zmul d e)))
          (Zmul b (Zadd (Zmul c e) (Zmul D (Zmul d f)))))
        (Zadd (Zadd ACF ADE) (Zadd BCE DBDF)) := by
    have first :
        Zeq (Zmul a (Zadd (Zmul c f) (Zmul d e)))
          (Zadd ACF ADE) :=
      R.left_distrib a (Zmul c f) (Zmul d e)
    have second :
        Zeq (Zmul b (Zadd (Zmul c e) (Zmul D (Zmul d f))))
          (Zadd BCE DBDF) := by
      exact R.trans (R.left_distrib b (Zmul c e) (Zmul D (Zmul d f)))
        (R.add_congr
          (R.refl BCE)
          (zmul_left_nested_swap b D d f))
    exact R.add_congr first second
  have permuted :
      Zeq (Zadd (Zadd ACF DBDF) (Zadd ADE BCE))
        (Zadd (Zadd ACF ADE) (Zadd BCE DBDF)) := by
    exact R.trans (zadd_four_swap ACF DBDF ADE BCE)
      (zadd_left (a := Zadd DBDF BCE) (b := Zadd BCE DBDF)
        (c := Zadd ACF ADE)
        (R.add_comm DBDF BCE))
  exact R.trans leftStructured (R.trans permuted (R.symm rightStructured))

theorem pellPairMul_assoc (D : Z) (a b c : PellPair) :
    PellPairEq (pellPairMul D (pellPairMul D a b) c)
      (pellPairMul D a (pellPairMul D b c)) := by
  constructor
  · exact pellPairMul_assoc_x_expr D a.x a.y b.x b.y c.x c.y
  · exact pellPairMul_assoc_y_expr D a.x a.y b.x b.y c.x c.y

theorem pellPairMul_one (D : Z) (a : PellPair) :
    PellPairEq (pellPairMul D a pellPairOne) a := by
  constructor
  · exact R.trans
      (R.add_congr
        (R.mul_one a.x)
        (R.trans
          (zmul_left (a := Zmul a.y Zzero) (b := Zzero) (c := D)
            (R.mul_zero a.y))
          (R.mul_zero D)))
      (R.add_zero a.x)
  · exact R.trans
      (R.add_congr (R.mul_zero a.x) (R.mul_one a.y))
      (R.zero_add a.y)

theorem pellPairOne_mul (D : Z) (a : PellPair) :
    PellPairEq (pellPairMul D pellPairOne a) a :=
  PellPairEq_trans (pellPairMul_comm D pellPairOne a) (pellPairMul_one D a)

theorem pellPairMul_conj_norm (D : Z) (a : PellPair) :
    PellPairEq (pellPairMul D a (pellPairInv a))
      (pellPairOfInt (pellNorm D a.x a.y)) := by
  constructor
  · exact R.add_congr
      (R.refl (zsq a.x))
      (R.trans
        (zmul_left (a := Zmul a.y (Zneg a.y)) (b := Zneg (zsq a.y)) (c := D)
          (zmul_neg_right a.y a.y))
        (zmul_neg_right D (zsq a.y)))
  · exact R.trans
      (R.add_congr
        (zmul_neg_right a.x a.y)
        (R.mul_comm a.y a.x))
      (R.neg_add (Zmul a.x a.y))

theorem pellPairMul_inv (D : Z) (a : PellPair) :
    IsPellSolution D a.x a.y ->
      PellPairEq (pellPairMul D a (pellPairInv a)) pellPairOne := by
  intro h
  have normEq := pellPairMul_conj_norm D a
  constructor
  · exact R.trans normEq.left h
  · exact normEq.right

theorem pellPairInv_mul (D : Z) (a : PellPair) :
    IsPellSolution D a.x a.y ->
      PellPairEq (pellPairMul D (pellPairInv a) a) pellPairOne := by
  intro h
  exact PellPairEq_trans (pellPairMul_comm D (pellPairInv a) a)
    (pellPairMul_inv D a h)

theorem pellPairInv_mul_self_norm (D : Z) (a : PellPair) :
    PellPairEq (pellPairMul D (pellPairInv a) a)
      (pellPairOfInt (pellNorm D a.x a.y)) :=
  PellPairEq_trans (pellPairMul_comm D (pellPairInv a) a)
    (pellPairMul_conj_norm D a)

theorem pellPairInv_mul_distrib (D : Z) (a b : PellPair) :
    PellPairEq (pellPairInv (pellPairMul D a b))
      (pellPairMul D (pellPairInv a) (pellPairInv b)) := by
  constructor
  · exact R.add_congr
      (R.refl (Zmul a.x b.x))
      (zmul_left (a := Zmul a.y b.y)
        (b := Zmul (Zneg a.y) (Zneg b.y))
        (c := D)
        (R.symm (zmul_neg_neg a.y b.y)))
  · exact R.trans (zneg_add (Zmul a.x b.y) (Zmul a.y b.x))
      (R.add_congr
        (R.symm (zmul_neg_right a.x b.y))
        (R.symm (zmul_neg_left a.y b.x)))

theorem pellPairOfInt_mul (D a b : Z) :
    PellPairEq (pellPairMul D (pellPairOfInt a) (pellPairOfInt b))
      (pellPairOfInt (Zmul a b)) := by
  constructor
  · exact R.trans
      (R.add_congr
        (R.refl (Zmul a b))
        (R.trans
          (zmul_left (a := Zmul Zzero Zzero) (b := Zzero) (c := D)
            (R.mul_zero Zzero))
          (R.mul_zero D)))
      (R.add_zero (Zmul a b))
  · exact R.trans
      (R.add_congr (R.mul_zero a) (R.zero_mul b))
      (R.add_zero Zzero)

theorem pellNorm_respects {D x x' y y' : Z} :
    Zeq x x' -> Zeq y y' -> Zeq (pellNorm D x y) (pellNorm D x' y') := by
  intro hx hy
  exact zsub_respects
    (R.mul_congr hx hx)
    (zmul_left (a := zsq y) (b := zsq y') (c := D)
      (R.mul_congr hy hy))

theorem pellNorm_mul (D : Z) (a b : PellPair) :
    Zeq (pellNorm D (pellPairMul D a b).x (pellPairMul D a b).y)
      (Zmul (pellNorm D a.x a.y) (pellNorm D b.x b.y)) := by
  let p := pellPairMul D a b
  have productNorm :
      PellPairEq (pellPairMul D p (pellPairInv p))
        (pellPairOfInt (pellNorm D p.x p.y)) :=
    pellPairMul_conj_norm D p
  have invProduct :
      PellPairEq (pellPairInv p)
        (pellPairMul D (pellPairInv a) (pellPairInv b)) :=
    pellPairInv_mul_distrib D a b
  have replaceInv :
      PellPairEq (pellPairMul D p (pellPairInv p))
        (pellPairMul D (pellPairMul D a b)
          (pellPairMul D (pellPairInv a) (pellPairInv b))) :=
    pellPairMul_respects (PellPairEq_refl p) invProduct
  have reassocLeft :
      PellPairEq
        (pellPairMul D (pellPairMul D a b)
          (pellPairMul D (pellPairInv a) (pellPairInv b)))
        (pellPairMul D a
          (pellPairMul D b (pellPairMul D (pellPairInv a) (pellPairInv b)))) :=
    pellPairMul_assoc D a b (pellPairMul D (pellPairInv a) (pellPairInv b))
  have moveInvA :
      PellPairEq
        (pellPairMul D b (pellPairMul D (pellPairInv a) (pellPairInv b)))
        (pellPairMul D (pellPairInv a) (pellPairMul D b (pellPairInv b))) := by
    exact PellPairEq_trans
      (PellPairEq_symm (pellPairMul_assoc D b (pellPairInv a) (pellPairInv b)))
      (PellPairEq_trans
        (pellPairMul_respects (pellPairMul_comm D b (pellPairInv a))
          (PellPairEq_refl (pellPairInv b)))
        (pellPairMul_assoc D (pellPairInv a) b (pellPairInv b)))
  have reassocRight :
      PellPairEq
        (pellPairMul D a
          (pellPairMul D (pellPairInv a) (pellPairMul D b (pellPairInv b))))
        (pellPairMul D (pellPairMul D a (pellPairInv a))
          (pellPairMul D b (pellPairInv b))) :=
    PellPairEq_symm
      (pellPairMul_assoc D a (pellPairInv a) (pellPairMul D b (pellPairInv b)))
  have toNormFactors :
      PellPairEq
        (pellPairMul D (pellPairMul D a b)
          (pellPairMul D (pellPairInv a) (pellPairInv b)))
        (pellPairMul D
          (pellPairOfInt (pellNorm D a.x a.y))
          (pellPairOfInt (pellNorm D b.x b.y))) := by
    exact PellPairEq_trans reassocLeft
      (PellPairEq_trans (pellPairMul_respects (PellPairEq_refl a) moveInvA)
        (PellPairEq_trans reassocRight
          (pellPairMul_respects
            (pellPairMul_conj_norm D a)
            (pellPairMul_conj_norm D b))))
  have productAsNorm :
      PellPairEq (pellPairOfInt (pellNorm D p.x p.y))
        (pellPairMul D
          (pellPairOfInt (pellNorm D a.x a.y))
          (pellPairOfInt (pellNorm D b.x b.y))) :=
    PellPairEq_trans (PellPairEq_symm productNorm)
      (PellPairEq_trans replaceInv toNormFactors)
  have productAsInt :
      PellPairEq
        (pellPairMul D
          (pellPairOfInt (pellNorm D a.x a.y))
          (pellPairOfInt (pellNorm D b.x b.y)))
        (pellPairOfInt (Zmul (pellNorm D a.x a.y) (pellNorm D b.x b.y))) :=
    pellPairOfInt_mul D (pellNorm D a.x a.y) (pellNorm D b.x b.y)
  exact R.trans productAsNorm.left productAsInt.left

theorem pellNorm_compose (D x1 y1 x2 y2 : Z) :
    Zeq
      (pellNorm D
        (pellComposeX D x1 y1 x2 y2)
        (pellComposeY D x1 y1 x2 y2))
      (Zmul (pellNorm D x1 y1) (pellNorm D x2 y2)) :=
  pellNorm_mul D { x := x1, y := y1 } { x := x2, y := y2 }

theorem pell_trivial_solution (D : Z) :
    IsPellSolution D Zone Zzero := by
  exact R.trans
    (zsub_respects
      (R.mul_one Zone)
      (R.trans (zmul_left (a := zsq Zzero) (b := Zzero) (c := D)
          (R.mul_zero Zzero))
        (R.mul_zero D)))
    (R.trans
      (zadd_left (a := Zneg Zzero) (b := Zzero) (c := Zone) zneg_zero)
      (R.add_zero Zone))

theorem pellNorm_neg_y (D x y : Z) :
    Zeq (pellNorm D x (Zneg y)) (pellNorm D x y) := by
  exact zsub_respects
    (R.refl (zsq x))
    (zmul_left (a := zsq (Zneg y)) (b := zsq y) (c := D)
      (zsq_neg y))

theorem brahmagupta_compose_isPellSolution
    (D x1 y1 x2 y2 : Z) :
    IsPellSolution D x1 y1 ->
      IsPellSolution D x2 y2 ->
        IsPellSolution D
          (pellComposeX D x1 y1 x2 y2)
          (pellComposeY D x1 y1 x2 y2) := by
  intro h1 h2
  exact R.trans (pellNorm_compose D x1 y1 x2 y2)
    (R.trans (R.mul_congr h1 h2) (R.mul_one Zone))

structure PellSolution (D : Z) where
  x : Z
  y : Z
  isPell : IsPellSolution D x y

def PellSolutionEq {D : Z} (a b : PellSolution D) : Prop :=
  Zeq a.x b.x ∧ Zeq a.y b.y

def pellSolutionOne (D : Z) : PellSolution D :=
  { x := Zone, y := Zzero, isPell := pell_trivial_solution D }

def pellSolutionMul {D : Z} (a b : PellSolution D) : PellSolution D :=
  { x := pellComposeX D a.x a.y b.x b.y,
    y := pellComposeY D a.x a.y b.x b.y,
    isPell := brahmagupta_compose_isPellSolution D a.x a.y b.x b.y
      a.isPell b.isPell }

def pellSolutionInv {D : Z} (a : PellSolution D) : PellSolution D :=
  { x := a.x,
    y := Zneg a.y,
    isPell := by
      exact R.trans
        (pellNorm_neg_y D a.x a.y)
        a.isPell }

def pellSolutionGenerated (D a b : Z)
    (h : IsPellSolution D a b) : Nat -> PellSolution D
  | Nat.zero => pellSolutionOne D
  | Nat.succ n => pellSolutionMul { x := a, y := b, isPell := h }
      (pellSolutionGenerated D a b h n)

theorem PellSolutionEq_refl {D : Z} (a : PellSolution D) :
    PellSolutionEq a a := by
  constructor
  · exact R.refl a.x
  · exact R.refl a.y

theorem PellSolutionEq_symm {D : Z} {a b : PellSolution D} :
    PellSolutionEq a b -> PellSolutionEq b a := by
  intro h
  constructor
  · exact R.symm h.left
  · exact R.symm h.right

theorem PellSolutionEq_trans {D : Z} {a b c : PellSolution D} :
    PellSolutionEq a b -> PellSolutionEq b c -> PellSolutionEq a c := by
  intro ab bc
  constructor
  · exact R.trans ab.left bc.left
  · exact R.trans ab.right bc.right

theorem pellSolutionMul_respects {D : Z} {a a' b b' : PellSolution D} :
    PellSolutionEq a a' -> PellSolutionEq b b' ->
      PellSolutionEq (pellSolutionMul a b) (pellSolutionMul a' b') := by
  intro ha hb
  constructor
  · exact R.add_congr
      (R.mul_congr ha.left hb.left)
      (zmul_left (a := Zmul a.y b.y) (b := Zmul a'.y b'.y) (c := D)
        (R.mul_congr ha.right hb.right))
  · exact R.add_congr
      (R.mul_congr ha.left hb.right)
      (R.mul_congr ha.right hb.left)

theorem pellSolutionMul_assoc {D : Z} (a b c : PellSolution D) :
    PellSolutionEq (pellSolutionMul (pellSolutionMul a b) c)
      (pellSolutionMul a (pellSolutionMul b c)) :=
  pellPairMul_assoc D { x := a.x, y := a.y } { x := b.x, y := b.y } { x := c.x, y := c.y }

theorem pellSolutionMul_comm {D : Z} (a b : PellSolution D) :
    PellSolutionEq (pellSolutionMul a b) (pellSolutionMul b a) :=
  pellPairMul_comm D { x := a.x, y := a.y } { x := b.x, y := b.y }

theorem pellSolutionMul_one {D : Z} (a : PellSolution D) :
    PellSolutionEq (pellSolutionMul a (pellSolutionOne D)) a :=
  pellPairMul_one D { x := a.x, y := a.y }

theorem pellSolutionOne_mul {D : Z} (a : PellSolution D) :
    PellSolutionEq (pellSolutionMul (pellSolutionOne D) a) a :=
  pellPairOne_mul D { x := a.x, y := a.y }

theorem pellSolutionMul_inv {D : Z} (a : PellSolution D) :
    PellSolutionEq (pellSolutionMul a (pellSolutionInv a)) (pellSolutionOne D) :=
  pellPairMul_inv D { x := a.x, y := a.y } a.isPell

theorem pellSolutionInv_mul {D : Z} (a : PellSolution D) :
    PellSolutionEq (pellSolutionMul (pellSolutionInv a) a) (pellSolutionOne D) :=
  pellPairInv_mul D { x := a.x, y := a.y } a.isPell

theorem pellSolutionMul_closed {D : Z} (a b : PellSolution D) :
    IsPellSolution D
      (pellSolutionMul a b).x
      (pellSolutionMul a b).y :=
  (pellSolutionMul a b).isPell

theorem pellSolutionGenerated_isPell (D a b : Z)
    (h : IsPellSolution D a b) (n : Nat) :
    IsPellSolution D
      (pellSolutionGenerated D a b h n).x
      (pellSolutionGenerated D a b h n).y :=
  (pellSolutionGenerated D a b h n).isPell

end BEDC.Derived.PellUp
