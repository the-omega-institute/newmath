import BEDC.Algebra.Rel.IntegerUp

namespace BEDC.Derived.DualNumberUp

private abbrev Z := BEDC.Algebra.Rel.IntegerUp
private abbrev Zeq := BEDC.Algebra.Rel.IntEq
private abbrev Zzero := BEDC.Algebra.Rel.intZero
private abbrev Zone := BEDC.Algebra.Rel.intOne
private abbrev Zadd := BEDC.Algebra.Rel.IntAdd
private abbrev Zmul := BEDC.Algebra.Rel.IntMul
private abbrev Zneg := BEDC.Algebra.Rel.IntNeg

private def zring : BEDC.Algebra.Rel.RelCommRing Z Zeq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

structure DualNumber where
  base : Z
  eps : Z

def DualEq (x y : DualNumber) : Prop :=
  Zeq x.base y.base ∧ Zeq x.eps y.eps

def dualMk (a b : Z) : DualNumber :=
  { base := a, eps := b }

def dualZero : DualNumber :=
  dualMk Zzero Zzero

def dualOne : DualNumber :=
  dualMk Zone Zzero

def dualEpsilon : DualNumber :=
  dualMk Zzero Zone

def dualAdd (x y : DualNumber) : DualNumber :=
  dualMk (Zadd x.base y.base) (Zadd x.eps y.eps)

def dualNeg (x : DualNumber) : DualNumber :=
  dualMk (Zneg x.base) (Zneg x.eps)

def dualMul (x y : DualNumber) : DualNumber :=
  dualMk (Zmul x.base y.base)
    (Zadd (Zmul x.base y.eps) (Zmul x.eps y.base))

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

private theorem dualMul_assoc_eps_expr (a b c d e f : Z) :
    Zeq
      (Zadd (Zmul (Zmul a c) f)
        (Zmul (Zadd (Zmul a d) (Zmul b c)) e))
      (Zadd (Zmul a (Zadd (Zmul c f) (Zmul d e)))
        (Zmul b (Zmul c e))) := by
  have leftStructured :
      Zeq
        (Zadd (Zmul (Zmul a c) f)
          (Zmul (Zadd (Zmul a d) (Zmul b c)) e))
        (Zadd (Zadd (Zmul (Zmul a c) f) (Zmul (Zmul a d) e))
          (Zmul (Zmul b c) e)) := by
    exact zring.trans
      (zring.add_congr
        (zring.refl (Zmul (Zmul a c) f))
        (zring.right_distrib (Zmul a d) (Zmul b c) e))
      (zring.symm
        (zring.add_assoc
          (Zmul (Zmul a c) f)
          (Zmul (Zmul a d) e)
          (Zmul (Zmul b c) e)))
  have rightStructured :
      Zeq
        (Zadd (Zmul a (Zadd (Zmul c f) (Zmul d e)))
          (Zmul b (Zmul c e)))
        (Zadd (Zadd (Zmul (Zmul a c) f) (Zmul (Zmul a d) e))
          (Zmul (Zmul b c) e)) := by
    exact zring.trans
      (zring.add_congr
        (zring.left_distrib a (Zmul c f) (Zmul d e))
        (zring.refl (Zmul b (Zmul c e))))
      (zring.add_congr
        (zring.add_congr
          (zring.symm (zring.mul_assoc a c f))
          (zring.symm (zring.mul_assoc a d e)))
        (zring.symm (zring.mul_assoc b c e)))
  exact zring.trans leftStructured (zring.symm rightStructured)

private theorem dualMul_add_distrib_eps_expr (a b c d e f : Z) :
    Zeq
      (Zadd (Zmul a (Zadd d f)) (Zmul b (Zadd c e)))
      (Zadd (Zadd (Zmul a d) (Zmul b c))
        (Zadd (Zmul a f) (Zmul b e))) := by
  exact zring.trans
    (zring.add_congr
      (zring.left_distrib a d f)
      (zring.left_distrib b c e))
    (zadd_four_swap (Zmul a d) (Zmul a f) (Zmul b c) (Zmul b e))

theorem DualEq_refl (x : DualNumber) :
    DualEq x x := by
  constructor
  · exact zring.refl x.base
  · exact zring.refl x.eps

theorem DualEq_symm {x y : DualNumber} :
    DualEq x y -> DualEq y x := by
  intro h
  constructor
  · exact zring.symm h.left
  · exact zring.symm h.right

theorem DualEq_trans {x y z : DualNumber} :
    DualEq x y -> DualEq y z -> DualEq x z := by
  intro xy yz
  constructor
  · exact zring.trans xy.left yz.left
  · exact zring.trans xy.right yz.right

theorem dualAdd_respects {x x' y y' : DualNumber} :
    DualEq x x' -> DualEq y y' ->
      DualEq (dualAdd x y) (dualAdd x' y') := by
  intro hx hy
  constructor
  · exact zring.add_congr hx.left hy.left
  · exact zring.add_congr hx.right hy.right

theorem dualNeg_respects {x y : DualNumber} :
    DualEq x y -> DualEq (dualNeg x) (dualNeg y) := by
  intro h
  constructor
  · exact zring.neg_congr h.left
  · exact zring.neg_congr h.right

theorem dualMul_respects {x x' y y' : DualNumber} :
    DualEq x x' -> DualEq y y' ->
      DualEq (dualMul x y) (dualMul x' y') := by
  intro hx hy
  constructor
  · exact zring.mul_congr hx.left hy.left
  · exact zring.add_congr
      (zring.mul_congr hx.left hy.right)
      (zring.mul_congr hx.right hy.left)

theorem dualAdd_comm (x y : DualNumber) :
    DualEq (dualAdd x y) (dualAdd y x) := by
  constructor
  · exact zring.add_comm x.base y.base
  · exact zring.add_comm x.eps y.eps

theorem dualAdd_assoc (x y z : DualNumber) :
    DualEq (dualAdd (dualAdd x y) z) (dualAdd x (dualAdd y z)) := by
  constructor
  · exact zring.add_assoc x.base y.base z.base
  · exact zring.add_assoc x.eps y.eps z.eps

theorem dualAdd_zero (x : DualNumber) :
    DualEq (dualAdd x dualZero) x := by
  constructor
  · exact zring.add_zero x.base
  · exact zring.add_zero x.eps

theorem dualZero_add (x : DualNumber) :
    DualEq (dualAdd dualZero x) x := by
  constructor
  · exact zring.zero_add x.base
  · exact zring.zero_add x.eps

theorem dualAdd_neg (x : DualNumber) :
    DualEq (dualAdd x (dualNeg x)) dualZero := by
  constructor
  · exact zring.add_neg x.base
  · exact zring.add_neg x.eps

theorem dualNeg_add (x : DualNumber) :
    DualEq (dualAdd (dualNeg x) x) dualZero := by
  constructor
  · exact zring.neg_add x.base
  · exact zring.neg_add x.eps

theorem dualMul_comm (x y : DualNumber) :
    DualEq (dualMul x y) (dualMul y x) := by
  constructor
  · exact zring.mul_comm x.base y.base
  · exact zring.trans
      (zring.add_congr
        (zring.mul_comm x.base y.eps)
        (zring.mul_comm x.eps y.base))
      (zring.add_comm (Zmul y.eps x.base) (Zmul y.base x.eps))

theorem dualMul_assoc (x y z : DualNumber) :
    DualEq (dualMul (dualMul x y) z) (dualMul x (dualMul y z)) := by
  constructor
  · exact zring.mul_assoc x.base y.base z.base
  · exact dualMul_assoc_eps_expr x.base x.eps y.base y.eps z.base z.eps

theorem dualMul_one (x : DualNumber) :
    DualEq (dualMul x dualOne) x := by
  constructor
  · exact zring.mul_one x.base
  · exact zring.trans
      (zring.add_congr
        (zring.mul_zero x.base)
        (zring.mul_one x.eps))
      (zring.zero_add x.eps)

theorem dualOne_mul (x : DualNumber) :
    DualEq (dualMul dualOne x) x := by
  constructor
  · exact zring.one_mul x.base
  · exact zring.trans
      (zring.add_congr
        (zring.one_mul x.eps)
        (zring.zero_mul x.base))
      (zring.add_zero x.eps)

theorem dualMul_zero (x : DualNumber) :
    DualEq (dualMul x dualZero) dualZero := by
  constructor
  · exact zring.mul_zero x.base
  · exact zring.trans
      (zring.add_congr
        (zring.mul_zero x.base)
        (zring.mul_zero x.eps))
      (zring.add_zero Zzero)

theorem dualZero_mul (x : DualNumber) :
    DualEq (dualMul dualZero x) dualZero := by
  constructor
  · exact zring.zero_mul x.base
  · exact zring.trans
      (zring.add_congr
        (zring.zero_mul x.eps)
        (zring.zero_mul x.base))
      (zring.add_zero Zzero)

theorem dualMul_add_distrib (x y z : DualNumber) :
    DualEq (dualMul x (dualAdd y z))
      (dualAdd (dualMul x y) (dualMul x z)) := by
  constructor
  · exact zring.left_distrib x.base y.base z.base
  · exact dualMul_add_distrib_eps_expr x.base x.eps y.base y.eps z.base z.eps

theorem dualMul_add_distrib_right (x y z : DualNumber) :
    DualEq (dualMul (dualAdd x y) z)
      (dualAdd (dualMul x z) (dualMul y z)) := by
  exact DualEq_trans (dualMul_comm (dualAdd x y) z)
    (DualEq_trans (dualMul_add_distrib z x y)
      (dualAdd_respects (dualMul_comm z x) (dualMul_comm z y)))

theorem dualMul_coefficients (a b c d : Z) :
    DualEq (dualMul (dualMk a b) (dualMk c d))
      (dualMk (Zmul a c) (Zadd (Zmul a d) (Zmul b c))) := by
  constructor
  · exact zring.refl (Zmul a c)
  · exact zring.refl (Zadd (Zmul a d) (Zmul b c))

theorem dualEpsilon_mul_self :
    DualEq (dualMul dualEpsilon dualEpsilon) dualZero := by
  constructor
  · exact zring.mul_zero Zzero
  · exact zring.trans
      (zring.add_congr
        (zring.zero_mul Zone)
        (zring.mul_zero Zone))
      (zring.add_zero Zzero)

structure DualNumberCommRingLaws where
  eq_refl : ∀ x : DualNumber, DualEq x x
  eq_symm : ∀ {x y : DualNumber}, DualEq x y -> DualEq y x
  eq_trans :
    ∀ {x y z : DualNumber}, DualEq x y -> DualEq y z -> DualEq x z
  add_respects :
    ∀ {x x' y y' : DualNumber}, DualEq x x' -> DualEq y y' ->
      DualEq (dualAdd x y) (dualAdd x' y')
  mul_respects :
    ∀ {x x' y y' : DualNumber}, DualEq x x' -> DualEq y y' ->
      DualEq (dualMul x y) (dualMul x' y')
  neg_respects :
    ∀ {x y : DualNumber}, DualEq x y -> DualEq (dualNeg x) (dualNeg y)
  add_comm : ∀ x y : DualNumber, DualEq (dualAdd x y) (dualAdd y x)
  add_assoc :
    ∀ x y z : DualNumber,
      DualEq (dualAdd (dualAdd x y) z) (dualAdd x (dualAdd y z))
  add_zero : ∀ x : DualNumber, DualEq (dualAdd x dualZero) x
  zero_add : ∀ x : DualNumber, DualEq (dualAdd dualZero x) x
  add_neg : ∀ x : DualNumber, DualEq (dualAdd x (dualNeg x)) dualZero
  neg_add : ∀ x : DualNumber, DualEq (dualAdd (dualNeg x) x) dualZero
  mul_comm : ∀ x y : DualNumber, DualEq (dualMul x y) (dualMul y x)
  mul_assoc :
    ∀ x y z : DualNumber,
      DualEq (dualMul (dualMul x y) z) (dualMul x (dualMul y z))
  mul_one : ∀ x : DualNumber, DualEq (dualMul x dualOne) x
  one_mul : ∀ x : DualNumber, DualEq (dualMul dualOne x) x
  mul_zero : ∀ x : DualNumber, DualEq (dualMul x dualZero) dualZero
  zero_mul : ∀ x : DualNumber, DualEq (dualMul dualZero x) dualZero
  left_distrib :
    ∀ x y z : DualNumber,
      DualEq (dualMul x (dualAdd y z))
        (dualAdd (dualMul x y) (dualMul x z))
  right_distrib :
    ∀ x y z : DualNumber,
      DualEq (dualMul (dualAdd x y) z)
        (dualAdd (dualMul x z) (dualMul y z))

def DualNumber_comm_ring_laws : DualNumberCommRingLaws where
  eq_refl := DualEq_refl
  eq_symm := by
    intro x y
    exact DualEq_symm
  eq_trans := by
    intro x y z
    exact DualEq_trans
  add_respects := by
    intro x x' y y'
    exact dualAdd_respects
  mul_respects := by
    intro x x' y y'
    exact dualMul_respects
  neg_respects := by
    intro x y
    exact dualNeg_respects
  add_comm := dualAdd_comm
  add_assoc := dualAdd_assoc
  add_zero := dualAdd_zero
  zero_add := dualZero_add
  add_neg := dualAdd_neg
  neg_add := dualNeg_add
  mul_comm := dualMul_comm
  mul_assoc := dualMul_assoc
  mul_one := dualMul_one
  one_mul := dualOne_mul
  mul_zero := dualMul_zero
  zero_mul := dualZero_mul
  left_distrib := dualMul_add_distrib
  right_distrib := dualMul_add_distrib_right

instance DualNumber_RelEquiv :
    BEDC.Algebra.Rel.RelEquiv DualNumber where
  rel := DualEq
  refl := DualEq_refl
  symm := by
    intro x y
    exact DualEq_symm
  trans := by
    intro x y z
    exact DualEq_trans

instance DualNumber_RelCommRing :
    BEDC.Algebra.Rel.RelCommRing DualNumber DualEq where
  zero := dualZero
  one := dualOne
  add := dualAdd
  mul := dualMul
  neg := dualNeg
  refl := DualNumber_comm_ring_laws.eq_refl
  symm := by
    intro x y
    exact DualNumber_comm_ring_laws.eq_symm
  trans := by
    intro x y z
    exact DualNumber_comm_ring_laws.eq_trans
  add_congr := by
    intro x x' y y'
    exact DualNumber_comm_ring_laws.add_respects
  mul_congr := by
    intro x x' y y'
    exact DualNumber_comm_ring_laws.mul_respects
  neg_congr := by
    intro x y
    exact DualNumber_comm_ring_laws.neg_respects
  add_assoc := DualNumber_comm_ring_laws.add_assoc
  add_comm := DualNumber_comm_ring_laws.add_comm
  add_zero := DualNumber_comm_ring_laws.add_zero
  zero_add := DualNumber_comm_ring_laws.zero_add
  add_neg := DualNumber_comm_ring_laws.add_neg
  neg_add := DualNumber_comm_ring_laws.neg_add
  mul_assoc := DualNumber_comm_ring_laws.mul_assoc
  mul_comm := DualNumber_comm_ring_laws.mul_comm
  mul_one := DualNumber_comm_ring_laws.mul_one
  one_mul := DualNumber_comm_ring_laws.one_mul
  mul_zero := DualNumber_comm_ring_laws.mul_zero
  zero_mul := DualNumber_comm_ring_laws.zero_mul
  left_distrib := DualNumber_comm_ring_laws.left_distrib
  right_distrib := DualNumber_comm_ring_laws.right_distrib

end BEDC.Derived.DualNumberUp
