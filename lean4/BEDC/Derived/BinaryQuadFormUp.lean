import BEDC.Algebra.Rel.IntegerUp
import BEDC.Derived.IntUp.Order
import BEDC.Derived.SL2Up

set_option maxHeartbeats 1000000

namespace BEDC.Derived.BinaryQuadFormUp

abbrev Z := BEDC.Algebra.Rel.IntegerUp
abbrev Zeq := BEDC.Algebra.Rel.IntEq
abbrev Zzero := BEDC.Algebra.Rel.intZero
abbrev Zone := BEDC.Algebra.Rel.intOne
abbrev Zadd := BEDC.Algebra.Rel.IntAdd
abbrev Zmul := BEDC.Algebra.Rel.IntMul
abbrev Zneg := BEDC.Algebra.Rel.IntNeg

private def R : BEDC.Algebra.Rel.RelCommRing Z Zeq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

def zsub (a b : Z) : Z :=
  Zadd a (Zneg b)

def zsq (a : Z) : Z :=
  Zmul a a

def zdouble (a : Z) : Z :=
  Zadd a a

def ztwo : Z :=
  zdouble Zone

def zfour : Z :=
  zdouble ztwo

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

private theorem zadd_four_last_swap (a b c d : Z) :
    Zeq (Zadd (Zadd a b) (Zadd c d))
      (Zadd (Zadd a d) (Zadd c b)) := by
  exact R.trans
    (zadd_left (a := Zadd c d) (b := Zadd d c) (c := Zadd a b)
      (R.add_comm c d))
    (R.trans (zadd_four_swap a b d c)
      (zadd_left (a := Zadd b c) (b := Zadd c b) (c := Zadd a d)
        (R.add_comm b c)))

private theorem zadd_three_rotate (a b c : Z) :
    Zeq (Zadd a (Zadd b c)) (Zadd b (Zadd a c)) := by
  exact R.trans (R.symm (R.add_assoc a b c))
    (R.trans
      (R.add_congr (R.add_comm a b) (R.refl c))
      (R.add_assoc b a c))

private theorem zadd_right_zero (a : Z) :
    Zeq (Zadd a Zzero) a :=
  R.add_zero a

private theorem zadd_left_zero (a : Z) :
    Zeq (Zadd Zzero a) a :=
  R.zero_add a

private theorem zneg_zero :
    Zeq (Zneg Zzero) Zzero :=
  R.neg_zero

private theorem zneg_neg (a : Z) :
    Zeq (Zneg (Zneg a)) a :=
  R.neg_neg a

private theorem zneg_add (a b : Z) :
    Zeq (Zneg (Zadd a b)) (Zadd (Zneg a) (Zneg b)) := by
  have hzero :
      Zeq (Zadd (Zadd a b) (Zadd (Zneg a) (Zneg b))) Zzero := by
    exact R.trans (zadd_four_swap a b (Zneg a) (Zneg b))
      (R.trans
        (R.add_congr (R.add_neg a) (R.add_neg b))
        (R.add_zero Zzero))
  exact R.symm
    (R.eq_neg_of_add_eq_zero (a := Zadd a b)
      (b := Zadd (Zneg a) (Zneg b)) hzero)

private theorem zsub_respects {a a' b b' : Z} :
    Zeq a a' -> Zeq b b' -> Zeq (zsub a b) (zsub a' b') := by
  intro ha hb
  exact R.add_congr ha (R.neg_congr hb)

private theorem zmul_neg_left (a b : Z) :
    Zeq (Zmul (Zneg a) b) (Zneg (Zmul a b)) :=
  R.neg_mul a b

private theorem zmul_neg_right (a b : Z) :
    Zeq (Zmul a (Zneg b)) (Zneg (Zmul a b)) :=
  R.mul_neg a b

private theorem zmul_neg_neg (a b : Z) :
    Zeq (Zmul (Zneg a) (Zneg b)) (Zmul a b) :=
  R.neg_neg_mul_neg a b

private theorem zsq_neg (a : Z) :
    Zeq (zsq (Zneg a)) (zsq a) :=
  zmul_neg_neg a a

private theorem zmul_sub_left (a b c : Z) :
    Zeq (Zmul a (zsub b c)) (zsub (Zmul a b) (Zmul a c)) := by
  exact R.trans (R.left_distrib a b (Zneg c))
    (zadd_left (a := Zmul a (Zneg c))
      (b := Zneg (Zmul a c))
      (c := Zmul a b)
      (zmul_neg_right a c))

private theorem zmul_sub_right (a b c : Z) :
    Zeq (Zmul (zsub a b) c) (zsub (Zmul a c) (Zmul b c)) := by
  exact R.trans (R.right_distrib a (Zneg b) c)
    (zadd_left (a := Zmul (Zneg b) c)
      (b := Zneg (Zmul b c))
      (c := Zmul a c)
      (zmul_neg_left b c))

private theorem zsub_add_sub (a b c d : Z) :
    Zeq (zsub (Zadd a b) (Zadd c d))
      (Zadd (zsub a c) (zsub b d)) := by
  exact R.trans
    (zadd_left (a := Zneg (Zadd c d))
      (b := Zadd (Zneg c) (Zneg d))
      (c := Zadd a b)
      (zneg_add c d))
    (zadd_four_swap a b (Zneg c) (Zneg d))

private theorem zsub_add_cancel (x e y : Z) :
    Zeq (zsub (Zadd x e) (Zadd e y)) (zsub x y) := by
  exact R.trans
    (zadd_left (a := Zneg (Zadd e y))
      (b := Zadd (Zneg e) (Zneg y))
      (c := Zadd x e)
      (zneg_add e y))
    (R.trans
      (zadd_four_last_swap x e (Zneg e) (Zneg y))
      (R.trans
        (zadd_left (a := Zadd (Zneg e) e)
          (b := Zzero)
          (c := Zadd x (Zneg y))
          (R.neg_add e))
        (R.add_zero (zsub x y))))

private theorem zsub_common_left {x x' y z : Z} :
    Zeq x x' ->
      Zeq (zsub (Zadd x y) (Zadd x' z)) (zsub y z) := by
  intro sameCommon
  have negExpand :
      Zeq (zsub (Zadd x y) (Zadd x' z))
        (Zadd (Zadd x y) (Zadd (Zneg x') (Zneg z))) :=
    R.add_congr (R.refl (Zadd x y)) (zneg_add x' z)
  have commonAligned :
      Zeq (Zadd (Zadd x y) (Zadd (Zneg x') (Zneg z)))
        (Zadd (Zadd x y) (Zadd (Zneg x) (Zneg z))) :=
    R.add_congr (R.refl (Zadd x y))
      (R.add_congr (R.neg_congr (R.symm sameCommon)) (R.refl (Zneg z)))
  have paired :
      Zeq (Zadd (Zadd x y) (Zadd (Zneg x) (Zneg z)))
        (Zadd (Zadd x (Zneg x)) (Zadd y (Zneg z))) :=
    zadd_four_swap x y (Zneg x) (Zneg z)
  have collapsed :
      Zeq (Zadd (Zadd x (Zneg x)) (Zadd y (Zneg z)))
        (Zadd Zzero (zsub y z)) :=
    R.add_congr (R.add_neg x) (R.refl (zsub y z))
  exact R.trans negExpand
    (R.trans commonAligned
      (R.trans paired (R.trans collapsed (R.zero_add (zsub y z)))))

private theorem zsub_neg_neg_swap (x y : Z) :
    Zeq (zsub (Zneg x) (Zneg y)) (zsub y x) := by
  exact R.trans
    (zadd_left (a := Zneg (Zneg y)) (b := y) (c := Zneg x) (zneg_neg y))
    (R.add_comm (Zneg x) y)

private theorem zsub_neg_right (a b : Z) :
    Zeq (zsub a (Zneg b)) (Zadd a b) := by
  exact zadd_left (a := Zneg (Zneg b)) (b := b) (c := a) (zneg_neg b)

private theorem zsub_zero (a : Z) :
    Zeq (zsub a Zzero) a := by
  exact R.trans
    (R.add_congr (R.refl a) zneg_zero)
    (R.add_zero a)

private theorem zsub_sub_neg_right (a b : Z) :
    Zeq (zsub (zsub a b) (Zneg b)) a := by
  exact R.trans (zsub_neg_right (zsub a b) b)
    (R.trans (R.add_assoc a (Zneg b) b)
      (R.trans (zadd_left (a := Zadd (Zneg b) b) (b := Zzero) (c := a)
        (R.neg_add b)) (R.add_zero a)))

private theorem zsub_add_cancel_right (a b : Z) :
    Zeq (Zadd (zsub a b) b) a := by
  exact R.trans (R.add_assoc a (Zneg b) b)
    (R.trans (zadd_left (a := Zadd (Zneg b) b) (b := Zzero) (c := a)
      (R.neg_add b)) (R.add_zero a))

private theorem zsub_sub_sub (a b c d : Z) :
    Zeq (zsub (zsub a b) (zsub c d))
      (zsub (Zadd a d) (Zadd b c)) := by
  exact R.trans
    (zadd_left (a := Zneg (zsub c d))
      (b := zsub d c)
      (c := zsub a b)
      (R.trans (zneg_add c (Zneg d)) (zsub_neg_neg_swap c d)))
    (R.trans
      (zadd_four_swap a (Zneg b) d (Zneg c))
      (zadd_left (a := Zadd (Zneg b) (Zneg c))
        (b := Zneg (Zadd b c))
        (c := Zadd a d)
        (R.symm (zneg_add b c))))

private theorem zsub_sub_right_cancel (x e y : Z) :
    Zeq (zsub (zsub (Zadd x e) y) e) (zsub x y) := by
  have asSub :
      Zeq (zsub (zsub (Zadd x e) y) e)
        (zsub (zsub (Zadd x e) y) (zsub e Zzero)) :=
    zsub_respects (R.refl (zsub (Zadd x e) y))
      (R.symm (zsub_zero e))
  have rotate :
      Zeq (zsub (zsub (Zadd x e) y) (zsub e Zzero))
        (zsub (Zadd (Zadd x e) Zzero) (Zadd y e)) :=
    zsub_sub_sub (Zadd x e) y e Zzero
  have simplify :
      Zeq (zsub (Zadd (Zadd x e) Zzero) (Zadd y e))
        (zsub (Zadd x e) (Zadd e y)) :=
    zsub_respects (R.add_zero (Zadd x e)) (R.add_comm y e)
  exact R.trans asSub
    (R.trans rotate
      (R.trans simplify (zsub_add_cancel x e y)))

private theorem zadd_neg_pair_middle (b d : Z) :
    Zeq (Zadd (Zadd b (Zneg d)) (Zneg b)) (Zneg d) := by
  exact R.trans (R.add_assoc b (Zneg d) (Zneg b))
    (R.trans
      (zadd_left (a := Zadd (Zneg d) (Zneg b))
        (b := Zadd (Zneg b) (Zneg d))
        (c := b)
        (R.add_comm (Zneg d) (Zneg b)))
      (R.trans (R.symm (R.add_assoc b (Zneg b) (Zneg d)))
        (R.trans
          (zadd_right (a := Zadd b (Zneg b)) (b := Zzero) (c := Zneg d)
            (R.add_neg b))
          (R.zero_add (Zneg d)))))

private theorem zadd_pair_neg_right_cancel (d c : Z) :
    Zeq (Zadd (Zadd d c) (Zneg d)) c := by
  exact R.trans (R.add_assoc d c (Zneg d))
    (R.trans
      (zadd_left (a := Zadd c (Zneg d)) (b := Zadd (Zneg d) c) (c := d)
        (R.add_comm c (Zneg d)))
      (R.trans (R.symm (R.add_assoc d (Zneg d) c))
        (R.trans
          (zadd_right (a := Zadd d (Zneg d)) (b := Zzero) (c := c)
            (R.add_neg d))
          (R.zero_add c))))

private theorem zadd_self_left (a c : Z) :
    Zeq (Zadd a (Zadd a c)) (Zadd (zdouble a) c) :=
  R.symm (R.add_assoc a a c)

private theorem zmul_double_left (a b : Z) :
    Zeq (Zmul (zdouble a) b) (zdouble (Zmul a b)) :=
  R.right_distrib a a b

private theorem zmul_double_right (a b : Z) :
    Zeq (Zmul a (zdouble b)) (zdouble (Zmul a b)) :=
  R.left_distrib a b b

private theorem zdouble_respects {a b : Z} :
    Zeq a b -> Zeq (zdouble a) (zdouble b) := by
  intro h
  exact R.add_congr h h

private theorem zfour_mul (x : Z) :
    Zeq (Zmul zfour x) (zdouble (zdouble x)) := by
  unfold zfour ztwo zdouble
  have h1 :
      Zeq (Zmul (Zadd (Zadd Zone Zone) (Zadd Zone Zone)) x)
        (Zadd (Zmul (Zadd Zone Zone) x) (Zmul (Zadd Zone Zone) x)) :=
    R.right_distrib (Zadd Zone Zone) (Zadd Zone Zone) x
  have h2 :
      Zeq (Zadd (Zmul (Zadd Zone Zone) x) (Zmul (Zadd Zone Zone) x))
        (Zadd (Zadd x x) (Zadd x x)) :=
    R.add_congr
      (R.trans (R.right_distrib Zone Zone x)
        (R.add_congr (R.one_mul x) (R.one_mul x)))
      (R.trans (R.right_distrib Zone Zone x)
        (R.add_congr (R.one_mul x) (R.one_mul x)))
  exact R.trans h1 h2

private theorem zdouble_mul_double (a b : Z) :
    Zeq (Zmul (zdouble a) (zdouble b)) (Zmul zfour (Zmul a b)) := by
  have left :
      Zeq (Zmul (zdouble a) (zdouble b))
        (zdouble (Zmul a (zdouble b))) :=
    zmul_double_left a (zdouble b)
  have right :
      Zeq (zdouble (Zmul a (zdouble b)))
        (zdouble (zdouble (Zmul a b))) :=
    zdouble_respects (zmul_double_right a b)
  exact R.trans left (R.trans right (R.symm (zfour_mul (Zmul a b))))

private theorem zsq_double (a : Z) :
    Zeq (zsq (zdouble a)) (Zmul zfour (zsq a)) :=
  zdouble_mul_double a a

private theorem zsquare_add (a b : Z) :
    Zeq (zsq (Zadd a b))
      (Zadd (Zadd (zsq a) (Zmul a b)) (Zadd (Zmul a b) (zsq b))) := by
  have expanded :
      Zeq (Zmul (Zadd a b) (Zadd a b))
        (Zadd (Zmul (Zadd a b) a) (Zmul (Zadd a b) b)) :=
    R.left_distrib (Zadd a b) a b
  have leftExpand :
      Zeq (Zmul (Zadd a b) a) (Zadd (zsq a) (Zmul b a)) :=
    R.right_distrib a b a
  have rightExpand :
      Zeq (Zmul (Zadd a b) b) (Zadd (Zmul a b) (zsq b)) :=
    R.right_distrib a b b
  exact R.trans expanded
    (R.add_congr
      (R.trans leftExpand
        (R.add_congr (R.refl (zsq a)) (R.mul_comm b a)))
      rightExpand)

private theorem zadd_middle_collect (x y z : Z) :
    Zeq (Zadd (Zadd x y) (Zadd y z)) (Zadd (Zadd x (zdouble y)) z) := by
  exact R.trans (R.add_assoc x y (Zadd y z))
    (R.trans
      (zadd_left (a := Zadd y (Zadd y z)) (b := Zadd (zdouble y) z) (c := x)
        (R.symm (R.add_assoc y y z)))
      (R.symm (R.add_assoc x (zdouble y) z)))

private theorem zsquare_add_double (a b : Z) :
    Zeq (zsq (Zadd b (zdouble a)))
      (Zadd (Zadd (zsq b) (Zmul zfour (Zmul a b))) (Zmul zfour (zsq a))) := by
  have expanded := zsquare_add b (zdouble a)
  have each :
      Zeq (Zmul b (zdouble a)) (zdouble (Zmul a b)) := by
    exact R.trans (zmul_double_right b a)
      (zdouble_respects (R.mul_comm b a))
  have normalized :
      Zeq
        (Zadd (Zadd (zsq b) (Zmul b (zdouble a)))
          (Zadd (Zmul b (zdouble a)) (zsq (zdouble a))))
        (Zadd (Zadd (zsq b) (zdouble (zdouble (Zmul a b))))
          (Zmul zfour (zsq a))) := by
    exact R.trans
      (R.add_congr
        (R.add_congr (R.refl (zsq b)) each)
        (R.add_congr each (zsq_double a)))
      (zadd_middle_collect (zsq b) (zdouble (Zmul a b)) (Zmul zfour (zsq a)))
  exact R.trans expanded
    (R.trans normalized
      (R.add_congr
        (R.add_congr (R.refl (zsq b)) (R.symm (zfour_mul (Zmul a b))))
        (R.refl (Zmul zfour (zsq a)))))

private theorem zmul_add_three (a b c d : Z) :
    Zeq (Zmul a (Zadd b (Zadd c d)))
      (Zadd (Zmul a b) (Zadd (Zmul a c) (Zmul a d))) := by
  exact R.trans (R.left_distrib a b (Zadd c d))
    (R.add_congr (R.refl (Zmul a b)) (R.left_distrib a c d))

private theorem zmul_zfour_add_three (a b c : Z) :
    Zeq (Zmul zfour (Zmul a (Zadd a (Zadd b c))))
      (Zadd (Zadd (Zmul zfour (zsq a)) (Zmul zfour (Zmul a b)))
        (Zmul zfour (Zmul a c))) := by
  have inner :
      Zeq (Zmul a (Zadd a (Zadd b c)))
        (Zadd (zsq a) (Zadd (Zmul a b) (Zmul a c))) :=
    zmul_add_three a a b c
  have transported :
      Zeq (Zmul zfour (Zmul a (Zadd a (Zadd b c))))
        (Zmul zfour (Zadd (zsq a) (Zadd (Zmul a b) (Zmul a c)))) :=
    zmul_left inner
  exact R.trans transported
    (R.trans (zmul_add_three zfour (zsq a) (Zmul a b) (Zmul a c))
      (R.symm (R.add_assoc (Zmul zfour (zsq a))
        (Zmul zfour (Zmul a b)) (Zmul zfour (Zmul a c)))))

structure BinaryQuadForm where
  a : Z
  b : Z
  c : Z

def BinaryQuadFormEq (Q P : BinaryQuadForm) : Prop :=
  Zeq Q.a P.a ∧ Zeq Q.b P.b ∧ Zeq Q.c P.c

theorem BinaryQuadFormEq_refl (Q : BinaryQuadForm) :
    BinaryQuadFormEq Q Q := by
  constructor
  · exact R.refl Q.a
  · constructor
    · exact R.refl Q.b
    · exact R.refl Q.c

theorem BinaryQuadFormEq_symm {Q P : BinaryQuadForm} :
    BinaryQuadFormEq Q P -> BinaryQuadFormEq P Q := by
  intro h
  constructor
  · exact R.symm h.left
  · constructor
    · exact R.symm h.right.left
    · exact R.symm h.right.right

theorem BinaryQuadFormEq_trans {Q P H : BinaryQuadForm} :
    BinaryQuadFormEq Q P -> BinaryQuadFormEq P H -> BinaryQuadFormEq Q H := by
  intro qp ph
  constructor
  · exact R.trans qp.left ph.left
  · constructor
    · exact R.trans qp.right.left ph.right.left
    · exact R.trans qp.right.right ph.right.right

def eval (Q : BinaryQuadForm) (x y : Z) : Z :=
  Zadd (Zadd (Zmul Q.a (zsq x)) (Zmul Q.b (Zmul x y))) (Zmul Q.c (zsq y))

def discriminant (Q : BinaryQuadForm) : Z :=
  zsub (zsq Q.b) (Zmul zfour (Zmul Q.a Q.c))

def Represents (Q : BinaryQuadForm) (n : Z) : Prop :=
  ∃ x y : Z, Zeq (eval Q x y) n

def zle (x y : Z) : Prop :=
  BEDC.Derived.IntUp.pairLe
    (BEDC.Derived.RationalUp.intToPair x)
    (BEDC.Derived.RationalUp.intToPair y)

def zabsLe (x y : Z) : Prop :=
  zle x y ∧ zle (Zneg x) y

def Reduced (Q : BinaryQuadForm) : Prop :=
  zabsLe Q.b Q.a ∧ zle Q.a Q.c

theorem discriminant_respects {Q P : BinaryQuadForm} :
    BinaryQuadFormEq Q P -> Zeq (discriminant Q) (discriminant P) := by
  intro h
  exact zsub_respects
    (R.mul_congr h.right.left h.right.left)
    (zmul_left (a := Zmul Q.a Q.c) (b := Zmul P.a P.c) (c := zfour)
      (R.mul_congr h.left h.right.right))

inductive SL2Step where
  | swap
  | shear
  | shearInv

def sl2SwapMat : BEDC.Derived.MatrixUp.Mat2 :=
  { a00 := Zzero, a01 := Zneg Zone, a10 := Zone, a11 := Zzero }

def sl2ShearMat : BEDC.Derived.MatrixUp.Mat2 :=
  { a00 := Zone, a01 := Zone, a10 := Zzero, a11 := Zone }

def sl2ShearInvMat : BEDC.Derived.MatrixUp.Mat2 :=
  { a00 := Zone, a01 := Zneg Zone, a10 := Zzero, a11 := Zone }

private theorem det_shear_like (u : Z) :
    Zeq
      (BEDC.Derived.MatrixUp.det
        { a00 := Zone, a01 := u, a10 := Zzero, a11 := Zone })
      Zone := by
  unfold BEDC.Derived.MatrixUp.det
  have left : Zeq (Zmul Zone Zone) Zone :=
    R.one_mul Zone
  have right : Zeq (Zneg (Zmul u Zzero)) Zzero := by
    exact R.trans (R.neg_congr (R.mul_zero u)) zneg_zero
  exact R.trans (R.add_congr left right) (R.add_zero Zone)

theorem sl2ShearMat_det_one :
    BEDC.Derived.SL2Up.SL2Carrier sl2ShearMat := by
  unfold BEDC.Derived.SL2Up.SL2Carrier sl2ShearMat
  exact det_shear_like Zone

theorem sl2ShearInvMat_det_one :
    BEDC.Derived.SL2Up.SL2Carrier sl2ShearInvMat := by
  unfold BEDC.Derived.SL2Up.SL2Carrier sl2ShearInvMat
  exact det_shear_like (Zneg Zone)

theorem sl2SwapMat_det_one :
    BEDC.Derived.SL2Up.SL2Carrier sl2SwapMat := by
  unfold BEDC.Derived.SL2Up.SL2Carrier sl2SwapMat
  change Zeq
    (BEDC.Derived.MatrixUp.det
      { a00 := Zzero, a01 := Zneg Zone, a10 := Zone, a11 := Zzero })
    Zone
  unfold BEDC.Derived.MatrixUp.det
  have left : Zeq (Zmul Zzero Zzero) Zzero :=
    R.zero_mul Zzero
  have rightMul : Zeq (Zmul (Zneg Zone) Zone) (Zneg Zone) :=
    R.mul_one (Zneg Zone)
  have right : Zeq (Zneg (Zmul (Zneg Zone) Zone)) Zone :=
    R.trans (R.neg_congr rightMul) (zneg_neg Zone)
  exact R.trans (R.add_congr left right) (R.zero_add Zone)

def SL2Step.toSL2 : SL2Step -> BEDC.Derived.SL2Up.SL2
  | SL2Step.swap => { mat := sl2SwapMat, det_one := sl2SwapMat_det_one }
  | SL2Step.shear => { mat := sl2ShearMat, det_one := sl2ShearMat_det_one }
  | SL2Step.shearInv => { mat := sl2ShearInvMat, det_one := sl2ShearInvMat_det_one }

def actStep : SL2Step -> BinaryQuadForm -> BinaryQuadForm
  | SL2Step.swap, Q =>
      { a := Q.c, b := Zneg Q.b, c := Q.a }
  | SL2Step.shear, Q =>
      { a := Q.a, b := Zadd Q.b (zdouble Q.a), c := Zadd Q.a (Zadd Q.b Q.c) }
  | SL2Step.shearInv, Q =>
      { a := Q.a, b := zsub Q.b (zdouble Q.a), c := zsub (Zadd Q.a Q.c) Q.b }

def actWord : List SL2Step -> BinaryQuadForm -> BinaryQuadForm
  | [], Q => Q
  | step :: tail, Q => actWord tail (actStep step Q)

theorem actSwap_discriminant (Q : BinaryQuadForm) :
    Zeq (discriminant (actStep SL2Step.swap Q)) (discriminant Q) := by
  unfold actStep discriminant
  exact zsub_respects
    (zsq_neg Q.b)
    (zmul_left (a := Zmul Q.c Q.a) (b := Zmul Q.a Q.c) (c := zfour)
      (R.mul_comm Q.c Q.a))

set_option maxHeartbeats 4000000 in
private theorem shear_discriminant_core (a b c : Z) :
    Zeq
      (zsub (zsq (Zadd b (zdouble a)))
        (Zmul zfour (Zmul a (Zadd a (Zadd b c)))))
      (zsub (zsq b) (Zmul zfour (Zmul a c))) := by
  have squareExpanded :
      Zeq (zsq (Zadd b (zdouble a)))
        (Zadd (Zadd (zsq b) (Zmul zfour (Zmul a b))) (Zmul zfour (zsq a))) :=
    zsquare_add_double a b
  have productExpanded :
      Zeq (Zmul zfour (Zmul a (Zadd a (Zadd b c))))
        (Zadd (Zadd (Zmul zfour (zsq a)) (Zmul zfour (Zmul a b)))
          (Zmul zfour (Zmul a c))) :=
    zmul_zfour_add_three a b c
  have aligned :
      Zeq
        (zsub (zsq (Zadd b (zdouble a)))
          (Zmul zfour (Zmul a (Zadd a (Zadd b c)))))
        (zsub
          (Zadd (Zadd (zsq b) (Zmul zfour (Zmul a b))) (Zmul zfour (zsq a)))
          (Zadd (Zadd (Zmul zfour (zsq a)) (Zmul zfour (Zmul a b)))
            (Zmul zfour (Zmul a c)))) :=
    zsub_respects squareExpanded productExpanded
  have swapMiddle :
      Zeq
        (Zadd (Zadd (Zmul zfour (zsq a)) (Zmul zfour (Zmul a b)))
          (Zmul zfour (Zmul a c)))
        (Zadd (Zadd (Zmul zfour (Zmul a b)) (Zmul zfour (zsq a)))
          (Zmul zfour (Zmul a c))) :=
    zadd_right
      (a := Zadd (Zmul zfour (zsq a)) (Zmul zfour (Zmul a b)))
      (b := Zadd (Zmul zfour (Zmul a b)) (Zmul zfour (zsq a)))
      (c := Zmul zfour (Zmul a c))
      (R.add_comm (Zmul zfour (zsq a)) (Zmul zfour (Zmul a b)))
  have commonCancelled :
      Zeq
        (zsub
          (Zadd (Zadd (zsq b) (Zmul zfour (Zmul a b))) (Zmul zfour (zsq a)))
          (Zadd (Zadd (Zmul zfour (Zmul a b)) (Zmul zfour (zsq a)))
            (Zmul zfour (Zmul a c))))
        (zsub (zsq b) (Zmul zfour (Zmul a c))) := by
    let common := Zadd (Zmul zfour (Zmul a b)) (Zmul zfour (zsq a))
    have leftRebracket :
        Zeq
          (Zadd (Zadd (zsq b) (Zmul zfour (Zmul a b))) (Zmul zfour (zsq a)))
          (Zadd (zsq b) common) :=
      R.add_assoc (zsq b) (Zmul zfour (Zmul a b)) (Zmul zfour (zsq a))
    exact R.trans (zsub_respects leftRebracket (R.refl _))
      (zsub_add_cancel (zsq b) common (Zmul zfour (Zmul a c)))
  exact R.trans aligned
    (R.trans
      (zsub_respects (R.refl _) swapMiddle)
      commonCancelled)

theorem actShear_discriminant (Q : BinaryQuadForm) :
    Zeq (discriminant (actStep SL2Step.shear Q)) (discriminant Q) := by
  unfold actStep discriminant
  exact shear_discriminant_core Q.a Q.b Q.c

private theorem shearInv_tail_sum (a b c : Z) :
    Zeq (Zadd (zsub b (zdouble a)) (zsub (Zadd a c) b)) (zsub c a) := by
  have combine :
      Zeq (Zadd (zsub b (zdouble a)) (zsub (Zadd a c) b))
        (zsub (Zadd b (Zadd a c)) (Zadd (zdouble a) b)) :=
    R.symm (zsub_add_sub b (Zadd a c) (zdouble a) b)
  have num :
      Zeq (Zadd b (Zadd a c)) (Zadd c (Zadd b a)) := by
    exact R.trans (R.symm (R.add_assoc b a c))
      (R.add_comm (Zadd b a) c)
  have den :
      Zeq (Zadd (zdouble a) b) (Zadd (Zadd b a) a) := by
    exact R.trans (R.add_comm (zdouble a) b)
      (R.symm (R.add_assoc b a a))
  exact R.trans combine
    (R.trans (zsub_respects num den)
      (zsub_add_cancel c (Zadd b a) a))

private theorem shear_after_shearInv_shape (a b c : Z) :
    BinaryQuadFormEq
      (actStep SL2Step.shear
        (actStep SL2Step.shearInv { a := a, b := b, c := c }))
      { a := a, b := b, c := c } := by
  change BinaryQuadFormEq
    { a := a,
      b := Zadd (zsub b (zdouble a)) (zdouble a),
      c := Zadd a (Zadd (zsub b (zdouble a)) (zsub (Zadd a c) b)) }
    { a := a, b := b, c := c }
  unfold BinaryQuadFormEq
  constructor
  · exact R.refl a
  · constructor
    · exact zsub_add_cancel_right b (zdouble a)
    · exact R.trans
        (zadd_left (a := Zadd (zsub b (zdouble a)) (zsub (Zadd a c) b))
          (b := zsub c a)
          (c := a)
          (shearInv_tail_sum a b c))
        (R.trans (R.add_comm a (zsub c a))
          (zsub_add_cancel_right c a))

theorem actShearInv_discriminant (Q : BinaryQuadForm) :
    Zeq (discriminant (actStep SL2Step.shearInv Q)) (discriminant Q) := by
  cases Q with
  | mk a b c =>
      have roundTrip := shear_after_shearInv_shape a b c
      have shearPreserved :
          Zeq
            (discriminant
              (actStep SL2Step.shear
                (actStep SL2Step.shearInv { a := a, b := b, c := c })))
            (discriminant (actStep SL2Step.shearInv { a := a, b := b, c := c })) :=
        actShear_discriminant (actStep SL2Step.shearInv { a := a, b := b, c := c })
      exact R.trans (R.symm shearPreserved) (discriminant_respects roundTrip)

theorem actStep_discriminant (step : SL2Step) (Q : BinaryQuadForm) :
    Zeq (discriminant (actStep step Q)) (discriminant Q) := by
  cases step with
  | swap => exact actSwap_discriminant Q
  | shear => exact actShear_discriminant Q
  | shearInv => exact actShearInv_discriminant Q

theorem actWord_discriminant (steps : List SL2Step) (Q : BinaryQuadForm) :
    Zeq (discriminant (actWord steps Q)) (discriminant Q) := by
  induction steps generalizing Q with
  | nil =>
      exact R.refl (discriminant Q)
  | cons step tail ih =>
      unfold actWord
      exact R.trans (ih (actStep step Q)) (actStep_discriminant step Q)

end BEDC.Derived.BinaryQuadFormUp
