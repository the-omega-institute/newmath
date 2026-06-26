import BEDC.Algebra.Rel.IntegerUp
import BEDC.Derived.PellUp

namespace BEDC.Derived.QuadIntUp

abbrev Z := BEDC.Algebra.Rel.IntegerUp
abbrev Zeq := BEDC.Algebra.Rel.IntEq
abbrev Zzero := BEDC.Algebra.Rel.intZero
abbrev Zone := BEDC.Algebra.Rel.intOne
abbrev Zadd := BEDC.Algebra.Rel.IntAdd
abbrev Zmul := BEDC.Algebra.Rel.IntMul
abbrev Zneg := BEDC.Algebra.Rel.IntNeg

private def zring : BEDC.Algebra.Rel.RelCommRing Z Zeq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

def zsub (a b : Z) : Z :=
  Zadd a (Zneg b)

def zsq (a : Z) : Z :=
  Zmul a a

structure QuadInt (d : Z) where
  re : Z
  rad : Z

def QuadEq {d : Z} (x y : QuadInt d) : Prop :=
  Zeq x.re y.re ∧ Zeq x.rad y.rad

def quadMk {d : Z} (a b : Z) : QuadInt d :=
  { re := a, rad := b }

def quadZero {d : Z} : QuadInt d :=
  quadMk Zzero Zzero

def quadOne {d : Z} : QuadInt d :=
  quadMk Zone Zzero

def quadSqrt {d : Z} : QuadInt d :=
  quadMk Zzero Zone

def quadAdd {d : Z} (x y : QuadInt d) : QuadInt d :=
  quadMk (Zadd x.re y.re) (Zadd x.rad y.rad)

def quadNeg {d : Z} (x : QuadInt d) : QuadInt d :=
  quadMk (Zneg x.re) (Zneg x.rad)

def quadMul {d : Z} (x y : QuadInt d) : QuadInt d :=
  quadMk
    (Zadd (Zmul x.re y.re) (Zmul d (Zmul x.rad y.rad)))
    (Zadd (Zmul x.re y.rad) (Zmul x.rad y.re))

def quadConj {d : Z} (x : QuadInt d) : QuadInt d :=
  quadMk x.re (Zneg x.rad)

def quadOfInt {d : Z} (a : Z) : QuadInt d :=
  quadMk a Zzero

def quadNorm {d : Z} (x : QuadInt d) : Z :=
  zsub (zsq x.re) (Zmul d (zsq x.rad))

private def toPell {d : Z} (x : QuadInt d) :
    BEDC.Derived.PellUp.PellPair :=
  { x := x.re, y := x.rad }

private theorem zadd_right {a b c : Z} (h : Zeq a b) :
    Zeq (Zadd a c) (Zadd b c) :=
  zring.add_congr h (zring.refl c)

private theorem zadd_left {a b c : Z} (h : Zeq a b) :
    Zeq (Zadd c a) (Zadd c b) :=
  zring.add_congr (zring.refl c) h

private theorem zmul_left {a b c : Z} (h : Zeq a b) :
    Zeq (Zmul c a) (Zmul c b) :=
  zring.mul_congr (zring.refl c) h

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

private theorem zsub_respects {a a' b b' : Z} :
    Zeq a a' -> Zeq b b' -> Zeq (zsub a b) (zsub a' b') := by
  intro ha hb
  exact zring.add_congr ha (zring.neg_congr hb)

private theorem zneg_one_mul (a : Z) :
    Zeq (Zmul (Zneg Zone) a) (Zneg a) :=
  zring.trans (zring.neg_mul Zone a)
    (zring.neg_congr (zring.one_mul a))

theorem QuadEq_refl {d : Z} (x : QuadInt d) :
    QuadEq x x := by
  constructor
  · exact zring.refl x.re
  · exact zring.refl x.rad

theorem QuadEq_symm {d : Z} {x y : QuadInt d} :
    QuadEq x y -> QuadEq y x := by
  intro h
  constructor
  · exact zring.symm h.left
  · exact zring.symm h.right

theorem QuadEq_trans {d : Z} {x y z : QuadInt d} :
    QuadEq x y -> QuadEq y z -> QuadEq x z := by
  intro xy yz
  constructor
  · exact zring.trans xy.left yz.left
  · exact zring.trans xy.right yz.right

theorem quadAdd_respects {d : Z} {x x' y y' : QuadInt d} :
    QuadEq x x' -> QuadEq y y' ->
      QuadEq (quadAdd x y) (quadAdd x' y') := by
  intro hx hy
  constructor
  · exact zring.add_congr hx.left hy.left
  · exact zring.add_congr hx.right hy.right

theorem quadNeg_respects {d : Z} {x y : QuadInt d} :
    QuadEq x y -> QuadEq (quadNeg x) (quadNeg y) := by
  intro h
  constructor
  · exact zring.neg_congr h.left
  · exact zring.neg_congr h.right

theorem quadMul_respects {d : Z} {x x' y y' : QuadInt d} :
    QuadEq x x' -> QuadEq y y' ->
      QuadEq (quadMul x y) (quadMul x' y') := by
  intro hx hy
  constructor
  · exact zring.add_congr
      (zring.mul_congr hx.left hy.left)
      (zmul_left (a := Zmul x.rad y.rad) (b := Zmul x'.rad y'.rad)
        (c := d)
        (zring.mul_congr hx.right hy.right))
  · exact zring.add_congr
      (zring.mul_congr hx.left hy.right)
      (zring.mul_congr hx.right hy.left)

theorem quadAdd_comm {d : Z} (x y : QuadInt d) :
    QuadEq (quadAdd x y) (quadAdd y x) := by
  constructor
  · exact zring.add_comm x.re y.re
  · exact zring.add_comm x.rad y.rad

theorem quadAdd_assoc {d : Z} (x y z : QuadInt d) :
    QuadEq (quadAdd (quadAdd x y) z) (quadAdd x (quadAdd y z)) := by
  constructor
  · exact zring.add_assoc x.re y.re z.re
  · exact zring.add_assoc x.rad y.rad z.rad

theorem quadAdd_zero {d : Z} (x : QuadInt d) :
    QuadEq (quadAdd x quadZero) x := by
  constructor
  · exact zring.add_zero x.re
  · exact zring.add_zero x.rad

theorem quadZero_add {d : Z} (x : QuadInt d) :
    QuadEq (quadAdd quadZero x) x := by
  constructor
  · exact zring.zero_add x.re
  · exact zring.zero_add x.rad

theorem quadAdd_neg {d : Z} (x : QuadInt d) :
    QuadEq (quadAdd x (quadNeg x)) quadZero := by
  constructor
  · exact zring.add_neg x.re
  · exact zring.add_neg x.rad

theorem quadNeg_add {d : Z} (x : QuadInt d) :
    QuadEq (quadAdd (quadNeg x) x) quadZero := by
  constructor
  · exact zring.neg_add x.re
  · exact zring.neg_add x.rad

theorem quadMul_comm {d : Z} (x y : QuadInt d) :
    QuadEq (quadMul x y) (quadMul y x) := by
  constructor
  · exact zring.add_congr
      (zring.mul_comm x.re y.re)
      (zmul_left (a := Zmul x.rad y.rad) (b := Zmul y.rad x.rad)
        (c := d)
        (zring.mul_comm x.rad y.rad))
  · exact zring.trans
      (zring.add_congr
        (zring.mul_comm x.re y.rad)
        (zring.mul_comm x.rad y.re))
      (zring.add_comm (Zmul y.rad x.re) (Zmul y.re x.rad))

theorem quadMul_assoc {d : Z} (x y z : QuadInt d) :
    QuadEq (quadMul (quadMul x y) z) (quadMul x (quadMul y z)) :=
  BEDC.Derived.PellUp.pellPairMul_assoc d (toPell x) (toPell y) (toPell z)

theorem quadMul_one {d : Z} (x : QuadInt d) :
    QuadEq (quadMul x quadOne) x :=
  BEDC.Derived.PellUp.pellPairMul_one d (toPell x)

theorem quadOne_mul {d : Z} (x : QuadInt d) :
    QuadEq (quadMul quadOne x) x :=
  QuadEq_trans (quadMul_comm quadOne x) (quadMul_one x)

theorem quadMul_zero {d : Z} (x : QuadInt d) :
    QuadEq (quadMul x quadZero) quadZero := by
  constructor
  · exact zring.trans
      (zring.add_congr
        (zring.mul_zero x.re)
        (zring.trans
          (zmul_left (a := Zmul x.rad Zzero) (b := Zzero) (c := d)
            (zring.mul_zero x.rad))
          (zring.mul_zero d)))
      (zring.add_zero Zzero)
  · exact zring.trans
      (zring.add_congr (zring.mul_zero x.re) (zring.mul_zero x.rad))
      (zring.add_zero Zzero)

theorem quadZero_mul {d : Z} (x : QuadInt d) :
    QuadEq (quadMul quadZero x) quadZero :=
  QuadEq_trans (quadMul_comm quadZero x) (quadMul_zero x)

private theorem quadMul_add_distrib_re_expr
    (D a b c e f g : Z) :
    Zeq
      (Zadd (Zmul a (Zadd c f)) (Zmul D (Zmul b (Zadd e g))))
      (Zadd
        (Zadd (Zmul a c) (Zmul D (Zmul b e)))
        (Zadd (Zmul a f) (Zmul D (Zmul b g)))) := by
  let AC := Zmul a c
  let AF := Zmul a f
  let DBE := Zmul D (Zmul b e)
  let DBG := Zmul D (Zmul b g)
  have expanded :
      Zeq
        (Zadd (Zmul a (Zadd c f)) (Zmul D (Zmul b (Zadd e g))))
        (Zadd (Zadd AC AF) (Zadd DBE DBG)) := by
    exact zring.add_congr
      (zring.left_distrib a c f)
      (zring.trans
        (zmul_left
          (a := Zmul b (Zadd e g))
          (b := Zadd (Zmul b e) (Zmul b g))
          (c := D)
          (zring.left_distrib b e g))
        (zring.left_distrib D (Zmul b e) (Zmul b g)))
  exact zring.trans expanded (zadd_four_swap AC AF DBE DBG)

private theorem quadMul_add_distrib_rad_expr
    (a b c e f g : Z) :
    Zeq
      (Zadd (Zmul a (Zadd e g)) (Zmul b (Zadd c f)))
      (Zadd
        (Zadd (Zmul a e) (Zmul b c))
        (Zadd (Zmul a g) (Zmul b f))) := by
  exact zring.trans
    (zring.add_congr
      (zring.left_distrib a e g)
      (zring.left_distrib b c f))
    (zadd_four_swap (Zmul a e) (Zmul a g) (Zmul b c) (Zmul b f))

theorem quadMul_add_distrib {d : Z} (x y z : QuadInt d) :
    QuadEq (quadMul x (quadAdd y z))
      (quadAdd (quadMul x y) (quadMul x z)) := by
  constructor
  · exact quadMul_add_distrib_re_expr d x.re x.rad y.re y.rad z.re z.rad
  · exact quadMul_add_distrib_rad_expr x.re x.rad y.re y.rad z.re z.rad

theorem quadMul_add_distrib_right {d : Z} (x y z : QuadInt d) :
    QuadEq (quadMul (quadAdd x y) z)
      (quadAdd (quadMul x z) (quadMul y z)) := by
  exact QuadEq_trans (quadMul_comm (quadAdd x y) z)
    (QuadEq_trans (quadMul_add_distrib z x y)
      (quadAdd_respects (quadMul_comm z x) (quadMul_comm z y)))

theorem quadMul_coefficients {d : Z} (a b c e : Z) :
    QuadEq (quadMul (quadMk (d := d) a b) (quadMk c e))
      (quadMk
        (Zadd (Zmul a c) (Zmul d (Zmul b e)))
        (Zadd (Zmul a e) (Zmul b c))) := by
  constructor
  · exact zring.refl (Zadd (Zmul a c) (Zmul d (Zmul b e)))
  · exact zring.refl (Zadd (Zmul a e) (Zmul b c))

theorem quadSqrt_mul_self {d : Z} :
    QuadEq (quadMul (quadSqrt (d := d)) quadSqrt) (quadOfInt d) := by
  constructor
  · exact zring.trans
      (zring.add_congr
        (zring.zero_mul Zzero)
        (zring.trans
          (zmul_left (a := Zmul Zone Zone) (b := Zone) (c := d)
            (zring.mul_one Zone))
          (zring.mul_one d)))
      (zring.zero_add d)
  · exact zring.trans
      (zring.add_congr (zring.zero_mul Zone) (zring.mul_zero Zone))
      (zring.add_zero Zzero)

theorem quadConj_respects {d : Z} {x y : QuadInt d} :
    QuadEq x y -> QuadEq (quadConj x) (quadConj y) := by
  intro h
  constructor
  · exact h.left
  · exact zring.neg_congr h.right

theorem quadConj_involutive {d : Z} (x : QuadInt d) :
    QuadEq (quadConj (quadConj x)) x := by
  constructor
  · exact zring.refl x.re
  · exact zring.neg_neg x.rad

theorem quadConj_mul {d : Z} (x y : QuadInt d) :
    QuadEq (quadConj (quadMul x y))
      (quadMul (quadConj x) (quadConj y)) :=
  BEDC.Derived.PellUp.pellPairInv_mul_distrib d (toPell x) (toPell y)

theorem quadMul_conj_norm {d : Z} (x : QuadInt d) :
    QuadEq (quadMul x (quadConj x)) (quadOfInt (quadNorm x)) :=
  BEDC.Derived.PellUp.pellPairMul_conj_norm d (toPell x)

theorem quadConj_mul_self_norm {d : Z} (x : QuadInt d) :
    QuadEq (quadMul (quadConj x) x) (quadOfInt (quadNorm x)) :=
  QuadEq_trans (quadMul_comm (quadConj x) x) (quadMul_conj_norm x)

theorem quadOfInt_mul {d : Z} (a b : Z) :
    QuadEq (quadMul (quadOfInt (d := d) a) (quadOfInt b)) (quadOfInt (Zmul a b)) :=
  BEDC.Derived.PellUp.pellPairOfInt_mul d a b

theorem quadNorm_respects {d : Z} {x y : QuadInt d} :
    QuadEq x y -> Zeq (quadNorm x) (quadNorm y) := by
  intro h
  exact zsub_respects
    (zring.mul_congr h.left h.left)
    (zmul_left (a := zsq x.rad) (b := zsq y.rad) (c := d)
      (zring.mul_congr h.right h.right))

theorem quadNorm_mul {d : Z} (x y : QuadInt d) :
    Zeq (quadNorm (quadMul x y)) (Zmul (quadNorm x) (quadNorm y)) :=
  BEDC.Derived.PellUp.pellNorm_mul d (toPell x) (toPell y)

def gaussianQuadParameter : Z :=
  Zneg Zone

abbrev GaussianQuadInt := QuadInt gaussianQuadParameter

theorem gaussianQuad_mul_coefficients (a b c e : Z) :
    QuadEq
      (quadMul
        (quadMk (d := gaussianQuadParameter) a b)
        (quadMk c e))
      (quadMk
        (Zadd (Zmul a c) (Zneg (Zmul b e)))
        (Zadd (Zmul a e) (Zmul b c))) := by
  constructor
  · exact zring.add_congr
      (zring.refl (Zmul a c))
      (zneg_one_mul (Zmul b e))
  · exact zring.refl (Zadd (Zmul a e) (Zmul b c))

structure QuadIntCommRingLaws (d : Z) where
  eq_refl : ∀ x : QuadInt d, QuadEq x x
  eq_symm : ∀ {x y : QuadInt d}, QuadEq x y -> QuadEq y x
  eq_trans :
    ∀ {x y z : QuadInt d}, QuadEq x y -> QuadEq y z -> QuadEq x z
  add_respects :
    ∀ {x x' y y' : QuadInt d}, QuadEq x x' -> QuadEq y y' ->
      QuadEq (quadAdd x y) (quadAdd x' y')
  mul_respects :
    ∀ {x x' y y' : QuadInt d}, QuadEq x x' -> QuadEq y y' ->
      QuadEq (quadMul x y) (quadMul x' y')
  neg_respects :
    ∀ {x y : QuadInt d}, QuadEq x y -> QuadEq (quadNeg x) (quadNeg y)
  add_comm : ∀ x y : QuadInt d, QuadEq (quadAdd x y) (quadAdd y x)
  add_assoc :
    ∀ x y z : QuadInt d,
      QuadEq (quadAdd (quadAdd x y) z) (quadAdd x (quadAdd y z))
  add_zero : ∀ x : QuadInt d, QuadEq (quadAdd x quadZero) x
  zero_add : ∀ x : QuadInt d, QuadEq (quadAdd quadZero x) x
  add_neg : ∀ x : QuadInt d, QuadEq (quadAdd x (quadNeg x)) quadZero
  neg_add : ∀ x : QuadInt d, QuadEq (quadAdd (quadNeg x) x) quadZero
  mul_comm : ∀ x y : QuadInt d, QuadEq (quadMul x y) (quadMul y x)
  mul_assoc :
    ∀ x y z : QuadInt d,
      QuadEq (quadMul (quadMul x y) z) (quadMul x (quadMul y z))
  mul_one : ∀ x : QuadInt d, QuadEq (quadMul x quadOne) x
  one_mul : ∀ x : QuadInt d, QuadEq (quadMul quadOne x) x
  mul_zero : ∀ x : QuadInt d, QuadEq (quadMul x quadZero) quadZero
  zero_mul : ∀ x : QuadInt d, QuadEq (quadMul quadZero x) quadZero
  left_distrib :
    ∀ x y z : QuadInt d,
      QuadEq (quadMul x (quadAdd y z))
        (quadAdd (quadMul x y) (quadMul x z))
  right_distrib :
    ∀ x y z : QuadInt d,
      QuadEq (quadMul (quadAdd x y) z)
        (quadAdd (quadMul x z) (quadMul y z))

def QuadInt_comm_ring_laws (d : Z) : QuadIntCommRingLaws d where
  eq_refl := QuadEq_refl
  eq_symm := by
    intro x y
    exact QuadEq_symm
  eq_trans := by
    intro x y z
    exact QuadEq_trans
  add_respects := by
    intro x x' y y'
    exact quadAdd_respects
  mul_respects := by
    intro x x' y y'
    exact quadMul_respects
  neg_respects := by
    intro x y
    exact quadNeg_respects
  add_comm := quadAdd_comm
  add_assoc := quadAdd_assoc
  add_zero := quadAdd_zero
  zero_add := quadZero_add
  add_neg := quadAdd_neg
  neg_add := quadNeg_add
  mul_comm := quadMul_comm
  mul_assoc := quadMul_assoc
  mul_one := quadMul_one
  one_mul := quadOne_mul
  mul_zero := quadMul_zero
  zero_mul := quadZero_mul
  left_distrib := quadMul_add_distrib
  right_distrib := quadMul_add_distrib_right

instance QuadInt_RelEquiv (d : Z) :
    BEDC.Algebra.Rel.RelEquiv (QuadInt d) where
  rel := QuadEq
  refl := QuadEq_refl
  symm := by
    intro x y
    exact QuadEq_symm
  trans := by
    intro x y z
    exact QuadEq_trans

instance QuadInt_RelCommRing (d : Z) :
    BEDC.Algebra.Rel.RelCommRing (QuadInt d) QuadEq where
  zero := quadZero
  one := quadOne
  add := quadAdd
  mul := quadMul
  neg := quadNeg
  refl := (QuadInt_comm_ring_laws d).eq_refl
  symm := by
    intro x y
    exact (QuadInt_comm_ring_laws d).eq_symm
  trans := by
    intro x y z
    exact (QuadInt_comm_ring_laws d).eq_trans
  add_congr := by
    intro x x' y y'
    exact (QuadInt_comm_ring_laws d).add_respects
  mul_congr := by
    intro x x' y y'
    exact (QuadInt_comm_ring_laws d).mul_respects
  neg_congr := by
    intro x y
    exact (QuadInt_comm_ring_laws d).neg_respects
  add_assoc := (QuadInt_comm_ring_laws d).add_assoc
  add_comm := (QuadInt_comm_ring_laws d).add_comm
  add_zero := (QuadInt_comm_ring_laws d).add_zero
  zero_add := (QuadInt_comm_ring_laws d).zero_add
  add_neg := (QuadInt_comm_ring_laws d).add_neg
  neg_add := (QuadInt_comm_ring_laws d).neg_add
  mul_assoc := (QuadInt_comm_ring_laws d).mul_assoc
  mul_comm := (QuadInt_comm_ring_laws d).mul_comm
  mul_one := (QuadInt_comm_ring_laws d).mul_one
  one_mul := (QuadInt_comm_ring_laws d).one_mul
  mul_zero := (QuadInt_comm_ring_laws d).mul_zero
  zero_mul := (QuadInt_comm_ring_laws d).zero_mul
  left_distrib := (QuadInt_comm_ring_laws d).left_distrib
  right_distrib := (QuadInt_comm_ring_laws d).right_distrib

end BEDC.Derived.QuadIntUp
