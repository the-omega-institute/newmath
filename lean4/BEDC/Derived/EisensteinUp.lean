import BEDC.Derived.IntUp.CommRing

namespace BEDC.Derived.EisensteinUp

abbrev Z := BEDC.Algebra.Rel.IntegerUp
abbrev Zeq := BEDC.Algebra.Rel.IntEq
abbrev Zadd := BEDC.Algebra.Rel.IntAdd
abbrev Zmul := BEDC.Algebra.Rel.IntMul
abbrev Zneg := BEDC.Algebra.Rel.IntNeg
abbrev Zzero := BEDC.Algebra.Rel.intZero
abbrev Zone := BEDC.Algebra.Rel.intOne

private def zlaws : BEDC.Derived.IntUp.IntegerUpCommRingLaws :=
  BEDC.Derived.IntUp.IntegerUp_comm_ring_laws

structure EisInt where
  re : Z
  om : Z

def EisEq (z w : EisInt) : Prop :=
  Zeq z.re w.re ∧ Zeq z.om w.om

private def zsub (a b : Z) : Z :=
  Zadd a (Zneg b)

def eisZero : EisInt :=
  { re := Zzero, om := Zzero }

def eisOne : EisInt :=
  { re := Zone, om := Zzero }

def eisOmega : EisInt :=
  { re := Zzero, om := Zone }

def eisAdd (z w : EisInt) : EisInt :=
  { re := Zadd z.re w.re,
    om := Zadd z.om w.om }

def eisNeg (z : EisInt) : EisInt :=
  { re := Zneg z.re,
    om := Zneg z.om }

def eisMul (z w : EisInt) : EisInt :=
  { re := zsub (Zmul z.re w.re) (Zmul z.om w.om),
    om := zsub (Zadd (Zmul z.re w.om) (Zmul z.om w.re))
      (Zmul z.om w.om) }

def eisConj (z : EisInt) : EisInt :=
  { re := zsub z.re z.om,
    om := Zneg z.om }

def eisNorm (z : EisInt) : Z :=
  Zadd (zsub (Zmul z.re z.re) (Zmul z.re z.om))
    (Zmul z.om z.om)

def eisOfInt (x : Z) : EisInt :=
  { re := x, om := Zzero }

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

private theorem zneg_sub (a b : Z) :
    Zeq (Zneg (zsub a b)) (zsub b a) := by
  exact zlaws.eq_trans (zneg_add a (Zneg b))
    (zlaws.eq_trans
      (zlaws.add_respects (zlaws.eq_refl (Zneg a)) (zneg_neg b))
      (zlaws.add_comm (Zneg a) b))

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

private theorem zadd_three_rotate_left (a b c : Z) :
    Zeq (Zadd a (Zadd b c)) (Zadd b (Zadd c a)) := by
  exact zlaws.eq_trans (zlaws.add_comm a (Zadd b c))
    (zlaws.add_assoc b c a)

private theorem zsub_sub_sub (x y u v : Z) :
    Zeq (zsub (zsub x y) (zsub u v))
      (zsub (Zadd x v) (Zadd y u)) := by
  exact zlaws.eq_trans
    (zadd_left (a := Zneg (zsub u v)) (b := zsub v u) (c := zsub x y)
      (zneg_sub u v))
    (zlaws.eq_trans
      (zadd_four_swap x (Zneg y) v (Zneg u))
      (zadd_left (a := Zadd (Zneg y) (Zneg u))
        (b := Zneg (Zadd y u))
        (c := Zadd x v)
        (zlaws.eq_symm (zneg_add y u))))

private theorem zsub_add_cancel (x e y : Z) :
    Zeq (zsub (Zadd x e) (Zadd e y)) (zsub x y) := by
  exact zlaws.eq_trans
    (zadd_left (a := Zneg (Zadd e y))
      (b := Zadd (Zneg e) (Zneg y))
      (c := Zadd x e)
      (zneg_add e y))
    (zlaws.eq_trans
      (zadd_four_last_swap x e (Zneg e) (Zneg y))
      (zlaws.eq_trans
        (zadd_left (a := Zadd (Zneg e) e)
          (b := Zzero)
          (c := Zadd x (Zneg y))
          (zlaws.neg_add e))
        (zlaws.add_zero (zsub x y))))

private theorem zsub_neg_right (a b : Z) :
    Zeq (zsub a (Zneg b)) (Zadd a b) := by
  exact zlaws.add_respects (zlaws.eq_refl a) (zneg_neg b)

private theorem zsub_add_cancel_right (a b : Z) :
    Zeq (Zadd (zsub a b) b) a := by
  exact zlaws.eq_trans (zlaws.add_assoc a (Zneg b) b)
    (zlaws.eq_trans
      (zadd_left (a := Zadd (Zneg b) b) (b := Zzero) (c := a)
        (zlaws.neg_add b))
      (zlaws.add_zero a))

private theorem zsub_sub_neg_right (a b : Z) :
    Zeq (zsub (zsub a b) (Zneg b)) a :=
  zlaws.eq_trans (zsub_neg_right (zsub a b) b)
    (zsub_add_cancel_right a b)

private theorem zsub_neg_right_zero (a : Z) :
    Zeq (zsub Zzero (Zneg a)) a :=
  zlaws.eq_trans (zsub_neg_right Zzero a) (zlaws.zero_add a)

private theorem zsub_zero (a : Z) :
    Zeq (zsub a Zzero) a := by
  exact zlaws.eq_trans
    (zlaws.add_respects (zlaws.eq_refl a) zneg_zero)
    (zlaws.add_zero a)

private theorem zsub_sub_right_cancel (x e y : Z) :
    Zeq (zsub (zsub (Zadd x e) y) e) (zsub x y) := by
  have asSub :
      Zeq (zsub (zsub (Zadd x e) y) e)
        (zsub (zsub (Zadd x e) y) (zsub e Zzero)) :=
    zsub_respects (zlaws.eq_refl (zsub (Zadd x e) y))
      (zlaws.eq_symm (zsub_zero e))
  have rotate :
      Zeq (zsub (zsub (Zadd x e) y) (zsub e Zzero))
        (zsub (Zadd (Zadd x e) Zzero) (Zadd y e)) :=
    zsub_sub_sub (Zadd x e) y e Zzero
  have simplify :
      Zeq (zsub (Zadd (Zadd x e) Zzero) (Zadd y e))
        (zsub (Zadd x e) (Zadd e y)) :=
    zsub_respects (zlaws.add_zero (Zadd x e)) (zlaws.add_comm y e)
  exact zlaws.eq_trans asSub
    (zlaws.eq_trans rotate
      (zlaws.eq_trans simplify (zsub_add_cancel x e y)))

private theorem zsub_neg_neg_swap (x y : Z) :
    Zeq (zsub (Zneg x) (Zneg y)) (zsub y x) := by
  exact zlaws.eq_trans (zsub_neg_right (Zneg x) y)
    (zlaws.add_comm (Zneg x) y)

private theorem zneg_add_eq_zero_of_eq {a b : Z} :
    Zeq b a -> Zeq (Zadd (Zneg a) b) Zzero := by
  intro h
  exact zlaws.eq_trans
    (zadd_left (a := b) (b := a) (c := Zneg a) h)
    (zlaws.neg_add a)

private theorem zconj_norm_om_zero (a b : Z) :
    Zeq
      (Zadd (Zadd (Zneg (Zmul a b)) (zsub (Zmul b a) (Zmul b b)))
        (Zmul b b))
      Zzero := by
  exact zlaws.eq_trans
    (zlaws.add_assoc (Zneg (Zmul a b)) (zsub (Zmul b a) (Zmul b b)) (Zmul b b))
    (zlaws.eq_trans
      (zadd_left
        (a := Zadd (zsub (Zmul b a) (Zmul b b)) (Zmul b b))
        (b := Zmul b a)
        (c := Zneg (Zmul a b))
        (zsub_add_cancel_right (Zmul b a) (Zmul b b)))
      (zneg_add_eq_zero_of_eq (zlaws.mul_comm b a)))

private theorem zconj_norm_re (a b : Z) :
    Zeq (zsub (Zmul a (zsub a b)) (Zmul b (Zneg b)))
      (Zadd (zsub (Zmul a a) (Zmul a b)) (Zmul b b)) := by
  let x := zsub (Zmul a a) (Zmul a b)
  let y := Zmul b b
  have expand :
      Zeq (zsub (Zmul a (zsub a b)) (Zmul b (Zneg b)))
        (zsub x (Zneg y)) :=
    zsub_respects (zmul_sub_left a a b) (zmul_neg_right b b)
  have cancelNeg : Zeq (zsub x (Zneg y)) (Zadd x y) :=
    zlaws.add_respects (zlaws.eq_refl x) (zneg_neg y)
  exact zlaws.eq_trans expand cancelNeg

private theorem zconj_norm_om (a b : Z) :
    Zeq
      (zsub (Zadd (Zmul a (Zneg b)) (Zmul b (zsub a b)))
        (Zmul b (Zneg b)))
      Zzero := by
  exact zlaws.eq_trans
      (zsub_respects
        (zlaws.add_respects
          (zmul_neg_right a b)
          (zmul_sub_left b a b))
        (zmul_neg_right b b))
    (zlaws.eq_trans
      (zlaws.add_respects
        (zlaws.eq_refl
          (Zadd (Zneg (Zmul a b)) (zsub (Zmul b a) (Zmul b b))))
        (zneg_neg (Zmul b b)))
      (zconj_norm_om_zero a b))

private theorem zmul_sub_neg_right (a b d : Z) :
    Zeq (Zmul (zsub a b) (Zneg d)) (zsub (Zmul b d) (Zmul a d)) := by
  exact zlaws.eq_trans (zmul_sub_right a b (Zneg d))
    (zlaws.eq_trans
      (zsub_respects (zmul_neg_right a d) (zmul_neg_right b d))
      (zsub_neg_neg_swap (Zmul a d) (Zmul b d)))

private theorem zmul_neg_sub_left (b c d : Z) :
    Zeq (Zmul (Zneg b) (zsub c d)) (zsub (Zmul b d) (Zmul b c)) := by
  exact zlaws.eq_trans (zmul_sub_left (Zneg b) c d)
    (zlaws.eq_trans
      (zsub_respects (zmul_neg_left b c) (zmul_neg_left b d))
      (zsub_neg_neg_swap (Zmul b c) (Zmul b d)))

private theorem zmul_sub_sub (a b c d : Z) :
    Zeq (Zmul (zsub a b) (zsub c d))
      (zsub (Zadd (Zmul a c) (Zmul b d))
        (Zadd (Zmul a d) (Zmul b c))) := by
  exact zlaws.eq_trans (zmul_sub_left (zsub a b) c d)
    (zlaws.eq_trans
      (zsub_respects
        (zmul_sub_right a b c)
        (zmul_sub_right a b d))
      (zlaws.eq_trans
        (zsub_sub_sub (Zmul a c) (Zmul b c) (Zmul a d) (Zmul b d))
        (zsub_respects (zlaws.eq_refl (Zadd (Zmul a c) (Zmul b d)))
          (zlaws.add_comm (Zmul b c) (Zmul a d)))))

private theorem zconj_mul_re_left (a b c d : Z) :
    Zeq
      (zsub (zsub (Zmul a c) (Zmul b d))
        (zsub (Zadd (Zmul a d) (Zmul b c)) (Zmul b d)))
      (zsub (Zmul a c) (Zadd (Zmul a d) (Zmul b c))) := by
  exact zlaws.eq_trans
    (zsub_sub_sub (Zmul a c) (Zmul b d)
      (Zadd (Zmul a d) (Zmul b c)) (Zmul b d))
    (zsub_add_cancel (Zmul a c) (Zmul b d)
      (Zadd (Zmul a d) (Zmul b c)))

private theorem zconj_mul_re_right (a b c d : Z) :
    Zeq
      (zsub (Zmul (zsub a b) (zsub c d))
        (Zmul (Zneg b) (Zneg d)))
      (zsub (Zmul a c) (Zadd (Zmul a d) (Zmul b c))) := by
  exact zlaws.eq_trans
    (zsub_respects (zmul_sub_sub a b c d) (zmul_neg_neg b d))
    (zsub_sub_right_cancel (Zmul a c) (Zmul b d)
      (Zadd (Zmul a d) (Zmul b c)))

private theorem zconj_mul_om_right (a b c d : Z) :
    Zeq
      (zsub
        (Zadd (Zmul (zsub a b) (Zneg d))
          (Zmul (Zneg b) (zsub c d)))
        (Zmul (Zneg b) (Zneg d)))
      (zsub (Zmul b d) (Zadd (Zmul a d) (Zmul b c))) := by
  let u := Zmul b d
  let f := Zmul a d
  let e := Zmul b c
  have expanded :
      Zeq
        (zsub
          (Zadd (Zmul (zsub a b) (Zneg d))
            (Zmul (Zneg b) (zsub c d)))
          (Zmul (Zneg b) (Zneg d)))
        (zsub (Zadd (zsub u f) (zsub u e)) u) :=
    zsub_respects
      (zlaws.add_respects
        (zmul_sub_neg_right a b d)
        (zmul_neg_sub_left b c d))
      (zmul_neg_neg b d)
  have combine :
      Zeq (zsub (Zadd (zsub u f) (zsub u e)) u)
        (zsub (zsub (Zadd u u) (Zadd f e)) u) :=
    zsub_respects (zlaws.eq_symm (zsub_add_sub u u f e)) (zlaws.eq_refl u)
  exact zlaws.eq_trans expanded
    (zlaws.eq_trans combine (zsub_sub_right_cancel u u (Zadd f e)))

private theorem zsub_add_sub_sub_cancel (a e u d v : Z) :
    Zeq (zsub (Zadd (zsub a e) (zsub u d)) (zsub v e))
      (zsub (Zadd a u) (Zadd d v)) := by
  have combineNumerator :
      Zeq (Zadd (zsub a e) (zsub u d))
        (zsub (Zadd a u) (Zadd e d)) :=
    zlaws.eq_symm (zsub_add_sub a u e d)
  exact zlaws.eq_trans
    (zsub_respects combineNumerator (zlaws.eq_refl (zsub v e)))
    (zlaws.eq_trans
      (zsub_sub_sub (Zadd a u) (Zadd e d) v e)
      (zlaws.eq_trans
        (zsub_respects (zlaws.eq_refl (Zadd (Zadd a u) e))
          (zlaws.add_assoc e d v))
        (zsub_add_cancel (Zadd a u) e (Zadd d v))))

private theorem zsub_add_sub_sub_cancel_second (u f c e w : Z) :
    Zeq (zsub (Zadd (zsub u f) (zsub c e)) (zsub w e))
      (zsub (Zadd u c) (Zadd f w)) := by
  exact zlaws.eq_trans
    (zsub_respects (zlaws.add_comm (zsub u f) (zsub c e))
      (zlaws.eq_refl (zsub w e)))
    (zlaws.eq_trans
      (zsub_add_sub_sub_cancel c e u f w)
      (zsub_respects (zlaws.add_comm c u) (zlaws.eq_refl (Zadd f w))))

private theorem eisMul_add_distrib_re_expr (a b c d e f : Z) :
    Zeq (zsub (Zmul a (Zadd c e)) (Zmul b (Zadd d f)))
      (Zadd (zsub (Zmul a c) (Zmul b d))
        (zsub (Zmul a e) (Zmul b f))) := by
  exact zlaws.eq_trans
    (zsub_respects
      (zlaws.left_distrib a c e)
      (zlaws.left_distrib b d f))
    (zsub_add_sub (Zmul a c) (Zmul a e) (Zmul b d) (Zmul b f))

private theorem eisMul_add_distrib_om_expr (a b c d e f : Z) :
    Zeq
      (zsub (Zadd (Zmul a (Zadd d f)) (Zmul b (Zadd c e)))
        (Zmul b (Zadd d f)))
      (Zadd (zsub (Zadd (Zmul a d) (Zmul b c)) (Zmul b d))
        (zsub (Zadd (Zmul a f) (Zmul b e)) (Zmul b f))) := by
  exact zlaws.eq_trans
    (zsub_respects
      (zlaws.add_respects
        (zlaws.left_distrib a d f)
        (zlaws.left_distrib b c e))
      (zlaws.left_distrib b d f))
    (zlaws.eq_trans
      (zsub_respects
        (zadd_four_swap (Zmul a d) (Zmul a f) (Zmul b c) (Zmul b e))
        (zlaws.eq_refl (Zadd (Zmul b d) (Zmul b f))))
      (zsub_add_sub (Zadd (Zmul a d) (Zmul b c))
        (Zadd (Zmul a f) (Zmul b e)) (Zmul b d) (Zmul b f)))

private theorem eisMul_assoc_re_expr (a b c d e f : Z) :
    Zeq
      (zsub (Zmul (zsub (Zmul a c) (Zmul b d)) e)
        (Zmul (zsub (Zadd (Zmul a d) (Zmul b c)) (Zmul b d)) f))
      (zsub (Zmul a (zsub (Zmul c e) (Zmul d f)))
        (Zmul b (zsub (Zadd (Zmul c f) (Zmul d e)) (Zmul d f)))) := by
  let ACE := Zmul (Zmul a c) e
  let BDE := Zmul (Zmul b d) e
  let ADF := Zmul (Zmul a d) f
  let BCF := Zmul (Zmul b c) f
  let BDF := Zmul (Zmul b d) f
  have leftSecond :
      Zeq
        (Zmul (zsub (Zadd (Zmul a d) (Zmul b c)) (Zmul b d)) f)
        (zsub (Zadd ADF BCF) BDF) :=
    zlaws.eq_trans
      (zmul_sub_right (Zadd (Zmul a d) (Zmul b c)) (Zmul b d) f)
      (zsub_respects
        (zlaws.right_distrib (Zmul a d) (Zmul b c) f)
        (zlaws.eq_refl BDF))
  have leftStructured :
      Zeq
        (zsub (Zmul (zsub (Zmul a c) (Zmul b d)) e)
          (Zmul (zsub (Zadd (Zmul a d) (Zmul b c)) (Zmul b d)) f))
        (zsub (Zadd ACE BDF) (Zadd BDE (Zadd ADF BCF))) :=
    zlaws.eq_trans
      (zsub_respects
        (zmul_sub_right (Zmul a c) (Zmul b d) e)
        leftSecond)
      (zsub_sub_sub ACE BDE (Zadd ADF BCF) BDF)
  let A_CE := Zmul a (Zmul c e)
  let A_DF := Zmul a (Zmul d f)
  let B_CF := Zmul b (Zmul c f)
  let B_DE := Zmul b (Zmul d e)
  let B_DF := Zmul b (Zmul d f)
  have rightSecond :
      Zeq
        (Zmul b (zsub (Zadd (Zmul c f) (Zmul d e)) (Zmul d f)))
        (zsub (Zadd B_CF B_DE) B_DF) :=
    zlaws.eq_trans
      (zmul_sub_left b (Zadd (Zmul c f) (Zmul d e)) (Zmul d f))
      (zsub_respects
        (zlaws.left_distrib b (Zmul c f) (Zmul d e))
        (zlaws.eq_refl B_DF))
  have rightStructured :
      Zeq
        (zsub (Zmul a (zsub (Zmul c e) (Zmul d f)))
          (Zmul b (zsub (Zadd (Zmul c f) (Zmul d e)) (Zmul d f))))
        (zsub (Zadd A_CE B_DF) (Zadd A_DF (Zadd B_CF B_DE))) :=
    zlaws.eq_trans
      (zsub_respects
        (zmul_sub_left a (Zmul c e) (Zmul d f))
        rightSecond)
      (zsub_sub_sub A_CE A_DF (Zadd B_CF B_DE) B_DF)
  have canonicalAlign :
      Zeq
        (zsub (Zadd ACE BDF) (Zadd BDE (Zadd ADF BCF)))
        (zsub (Zadd A_CE B_DF) (Zadd A_DF (Zadd B_CF B_DE))) :=
    zsub_respects
      (zlaws.add_respects (zlaws.mul_assoc a c e) (zlaws.mul_assoc b d f))
      (zlaws.eq_trans (zadd_three_rotate_left BDE ADF BCF)
        (zlaws.add_respects (zlaws.mul_assoc a d f)
          (zlaws.add_respects (zlaws.mul_assoc b c f) (zlaws.mul_assoc b d e))))
  exact zlaws.eq_trans leftStructured
    (zlaws.eq_trans canonicalAlign (zlaws.eq_symm rightStructured))

private theorem eisMul_assoc_om_expr (a b c d e f : Z) :
    Zeq
      (zsub
        (Zadd (Zmul (zsub (Zmul a c) (Zmul b d)) f)
          (Zmul (zsub (Zadd (Zmul a d) (Zmul b c)) (Zmul b d)) e))
        (Zmul (zsub (Zadd (Zmul a d) (Zmul b c)) (Zmul b d)) f))
      (zsub
        (Zadd
          (Zmul a (zsub (Zadd (Zmul c f) (Zmul d e)) (Zmul d f)))
          (Zmul b (zsub (Zmul c e) (Zmul d f))))
        (Zmul b (zsub (Zadd (Zmul c f) (Zmul d e)) (Zmul d f)))) := by
  let ACF := Zmul (Zmul a c) f
  let BDF := Zmul (Zmul b d) f
  let ADE := Zmul (Zmul a d) e
  let BCE := Zmul (Zmul b c) e
  let BDE := Zmul (Zmul b d) e
  let ADF := Zmul (Zmul a d) f
  let BCF := Zmul (Zmul b c) f
  have leftMiddleE :
      Zeq
        (Zmul (zsub (Zadd (Zmul a d) (Zmul b c)) (Zmul b d)) e)
        (zsub (Zadd ADE BCE) BDE) :=
    zlaws.eq_trans
      (zmul_sub_right (Zadd (Zmul a d) (Zmul b c)) (Zmul b d) e)
      (zsub_respects
        (zlaws.right_distrib (Zmul a d) (Zmul b c) e)
        (zlaws.eq_refl BDE))
  have leftMiddleF :
      Zeq
        (Zmul (zsub (Zadd (Zmul a d) (Zmul b c)) (Zmul b d)) f)
        (zsub (Zadd ADF BCF) BDF) :=
    zlaws.eq_trans
      (zmul_sub_right (Zadd (Zmul a d) (Zmul b c)) (Zmul b d) f)
      (zsub_respects
        (zlaws.right_distrib (Zmul a d) (Zmul b c) f)
        (zlaws.eq_refl BDF))
  have leftStructured :
      Zeq
        (zsub
          (Zadd (Zmul (zsub (Zmul a c) (Zmul b d)) f)
            (Zmul (zsub (Zadd (Zmul a d) (Zmul b c)) (Zmul b d)) e))
          (Zmul (zsub (Zadd (Zmul a d) (Zmul b c)) (Zmul b d)) f))
        (zsub (Zadd ACF (Zadd ADE BCE)) (Zadd BDE (Zadd ADF BCF))) :=
    zlaws.eq_trans
      (zsub_respects
        (zlaws.add_respects
          (zmul_sub_right (Zmul a c) (Zmul b d) f)
          leftMiddleE)
        leftMiddleF)
      (zsub_add_sub_sub_cancel ACF BDF (Zadd ADE BCE) BDE (Zadd ADF BCF))
  let A_CF := Zmul a (Zmul c f)
  let A_DE := Zmul a (Zmul d e)
  let A_DF := Zmul a (Zmul d f)
  let B_CE := Zmul b (Zmul c e)
  let B_DF := Zmul b (Zmul d f)
  let B_CF := Zmul b (Zmul c f)
  let B_DE := Zmul b (Zmul d e)
  have rightFirst :
      Zeq
        (Zmul a (zsub (Zadd (Zmul c f) (Zmul d e)) (Zmul d f)))
        (zsub (Zadd A_CF A_DE) A_DF) :=
    zlaws.eq_trans
      (zmul_sub_left a (Zadd (Zmul c f) (Zmul d e)) (Zmul d f))
      (zsub_respects
        (zlaws.left_distrib a (Zmul c f) (Zmul d e))
        (zlaws.eq_refl A_DF))
  have rightThird :
      Zeq
        (Zmul b (zsub (Zadd (Zmul c f) (Zmul d e)) (Zmul d f)))
        (zsub (Zadd B_CF B_DE) B_DF) :=
    zlaws.eq_trans
      (zmul_sub_left b (Zadd (Zmul c f) (Zmul d e)) (Zmul d f))
      (zsub_respects
        (zlaws.left_distrib b (Zmul c f) (Zmul d e))
        (zlaws.eq_refl B_DF))
  have rightStructured :
      Zeq
        (zsub
          (Zadd
            (Zmul a (zsub (Zadd (Zmul c f) (Zmul d e)) (Zmul d f)))
            (Zmul b (zsub (Zmul c e) (Zmul d f))))
          (Zmul b (zsub (Zadd (Zmul c f) (Zmul d e)) (Zmul d f))))
        (zsub (Zadd (Zadd A_CF A_DE) B_CE)
          (Zadd A_DF (Zadd B_CF B_DE))) :=
    zlaws.eq_trans
      (zsub_respects
        (zlaws.add_respects rightFirst
          (zmul_sub_left b (Zmul c e) (Zmul d f)))
        rightThird)
      (zsub_add_sub_sub_cancel_second (Zadd A_CF A_DE) A_DF B_CE B_DF
        (Zadd B_CF B_DE))
  have positiveAlign :
      Zeq (Zadd ACF (Zadd ADE BCE))
        (Zadd (Zadd A_CF A_DE) B_CE) :=
    zlaws.eq_trans
      (zlaws.add_respects (zlaws.mul_assoc a c f)
        (zlaws.add_respects (zlaws.mul_assoc a d e) (zlaws.mul_assoc b c e)))
      (zlaws.eq_symm (zlaws.add_assoc A_CF A_DE B_CE))
  have negativeAlign :
      Zeq (Zadd BDE (Zadd ADF BCF))
        (Zadd A_DF (Zadd B_CF B_DE)) :=
    zlaws.eq_trans (zadd_three_rotate_left BDE ADF BCF)
      (zlaws.add_respects (zlaws.mul_assoc a d f)
        (zlaws.add_respects (zlaws.mul_assoc b c f) (zlaws.mul_assoc b d e)))
  exact zlaws.eq_trans leftStructured
    (zlaws.eq_trans (zsub_respects positiveAlign negativeAlign)
      (zlaws.eq_symm rightStructured))

theorem EisEq_refl (z : EisInt) :
    EisEq z z := by
  constructor
  · exact zlaws.eq_refl z.re
  · exact zlaws.eq_refl z.om

theorem EisEq_symm {z w : EisInt} :
    EisEq z w -> EisEq w z := by
  intro h
  constructor
  · exact zlaws.eq_symm h.left
  · exact zlaws.eq_symm h.right

theorem EisEq_trans {x y z : EisInt} :
    EisEq x y -> EisEq y z -> EisEq x z := by
  intro xy yz
  constructor
  · exact zlaws.eq_trans xy.left yz.left
  · exact zlaws.eq_trans xy.right yz.right

theorem eisAdd_respects {x x' y y' : EisInt} :
    EisEq x x' -> EisEq y y' ->
      EisEq (eisAdd x y) (eisAdd x' y') := by
  intro hx hy
  constructor
  · exact zlaws.add_respects hx.left hy.left
  · exact zlaws.add_respects hx.right hy.right

theorem eisNeg_respects {x y : EisInt} :
    EisEq x y -> EisEq (eisNeg x) (eisNeg y) := by
  intro h
  constructor
  · exact zlaws.neg_respects h.left
  · exact zlaws.neg_respects h.right

theorem eisMul_respects {x x' y y' : EisInt} :
    EisEq x x' -> EisEq y y' ->
      EisEq (eisMul x y) (eisMul x' y') := by
  intro hx hy
  constructor
  · exact zsub_respects
      (zlaws.mul_respects hx.left hy.left)
      (zlaws.mul_respects hx.right hy.right)
  · exact zsub_respects
      (zlaws.add_respects
        (zlaws.mul_respects hx.left hy.right)
        (zlaws.mul_respects hx.right hy.left))
      (zlaws.mul_respects hx.right hy.right)

theorem eisAdd_comm (z w : EisInt) :
    EisEq (eisAdd z w) (eisAdd w z) := by
  constructor
  · exact zlaws.add_comm z.re w.re
  · exact zlaws.add_comm z.om w.om

theorem eisAdd_assoc (x y z : EisInt) :
    EisEq (eisAdd (eisAdd x y) z)
      (eisAdd x (eisAdd y z)) := by
  constructor
  · exact zlaws.add_assoc x.re y.re z.re
  · exact zlaws.add_assoc x.om y.om z.om

theorem eisAdd_zero (z : EisInt) :
    EisEq (eisAdd z eisZero) z := by
  constructor
  · exact zlaws.add_zero z.re
  · exact zlaws.add_zero z.om

theorem eisAdd_zero_left (z : EisInt) :
    EisEq (eisAdd eisZero z) z := by
  constructor
  · exact zlaws.zero_add z.re
  · exact zlaws.zero_add z.om

theorem eisAdd_neg (z : EisInt) :
    EisEq (eisAdd z (eisNeg z)) eisZero := by
  constructor
  · exact zlaws.add_neg z.re
  · exact zlaws.add_neg z.om

theorem eisAdd_neg_left (z : EisInt) :
    EisEq (eisAdd (eisNeg z) z) eisZero := by
  constructor
  · exact zlaws.neg_add z.re
  · exact zlaws.neg_add z.om

theorem eisMul_comm (z w : EisInt) :
    EisEq (eisMul z w) (eisMul w z) := by
  constructor
  · exact zsub_respects
      (zlaws.mul_comm z.re w.re)
      (zlaws.mul_comm z.om w.om)
  · exact zsub_respects
      (zlaws.eq_trans
        (zlaws.add_respects
          (zlaws.mul_comm z.re w.om)
          (zlaws.mul_comm z.om w.re))
        (zlaws.add_comm (Zmul w.om z.re) (Zmul w.re z.om)))
      (zlaws.mul_comm z.om w.om)

theorem eisMul_zero (z : EisInt) :
    EisEq (eisMul z eisZero) eisZero := by
  constructor
  · exact zlaws.eq_trans
      (zsub_respects (zlaws.mul_zero z.re) (zlaws.mul_zero z.om))
      (zlaws.add_zero Zzero)
  · exact zlaws.eq_trans
      (zsub_respects
        (zlaws.eq_trans
          (zlaws.add_respects (zlaws.mul_zero z.re) (zlaws.mul_zero z.om))
          (zlaws.add_zero Zzero))
        (zlaws.mul_zero z.om))
      (zlaws.add_zero Zzero)

theorem eisMul_zero_left (z : EisInt) :
    EisEq (eisMul eisZero z) eisZero :=
  EisEq_trans (eisMul_comm eisZero z) (eisMul_zero z)

theorem eisMul_one (z : EisInt) :
    EisEq (eisMul z eisOne) z := by
  constructor
  · exact zlaws.eq_trans
      (zsub_respects (zlaws.mul_one z.re) (zlaws.mul_zero z.om))
      (zlaws.add_zero z.re)
  · exact zlaws.eq_trans
      (zsub_respects
        (zlaws.eq_trans
          (zlaws.add_respects (zlaws.mul_zero z.re) (zlaws.mul_one z.om))
          (zlaws.zero_add z.om))
        (zlaws.mul_zero z.om))
      (zlaws.add_zero z.om)

theorem eisMul_one_left (z : EisInt) :
    EisEq (eisMul eisOne z) z :=
  EisEq_trans (eisMul_comm eisOne z) (eisMul_one z)

theorem eisMul_assoc (x y z : EisInt) :
    EisEq (eisMul (eisMul x y) z)
      (eisMul x (eisMul y z)) := by
  constructor
  · exact eisMul_assoc_re_expr x.re x.om y.re y.om z.re z.om
  · exact eisMul_assoc_om_expr x.re x.om y.re y.om z.re z.om

theorem eisMul_add_distrib (x y z : EisInt) :
    EisEq (eisMul x (eisAdd y z))
      (eisAdd (eisMul x y) (eisMul x z)) := by
  constructor
  · exact eisMul_add_distrib_re_expr x.re x.om y.re y.om z.re z.om
  · exact eisMul_add_distrib_om_expr x.re x.om y.re y.om z.re z.om

theorem eisMul_add_distrib_right (x y z : EisInt) :
    EisEq (eisMul (eisAdd x y) z)
      (eisAdd (eisMul x z) (eisMul y z)) := by
  exact EisEq_trans (eisMul_comm (eisAdd x y) z)
    (EisEq_trans (eisMul_add_distrib z x y)
      (eisAdd_respects (eisMul_comm z x) (eisMul_comm z y)))

theorem eisOmega_square :
    EisEq (eisMul eisOmega eisOmega) (eisNeg (eisAdd eisOmega eisOne)) := by
  constructor
  · exact zlaws.eq_trans
      (zsub_respects (zlaws.mul_zero Zzero) (zlaws.mul_one Zone))
      (zlaws.eq_trans (zlaws.zero_add (Zneg Zone))
        (zlaws.eq_symm (zlaws.zero_add (Zneg Zone))))
  · exact zlaws.eq_trans
      (zsub_respects
        (zlaws.eq_trans
          (zlaws.add_respects (zlaws.mul_zero Zone) (zlaws.mul_zero Zone))
          (zlaws.add_zero Zzero))
        (zlaws.mul_one Zone))
      (zlaws.eq_trans (zlaws.zero_add (Zneg Zone))
        (zlaws.eq_symm (zlaws.add_respects (zneg_zero) (zlaws.eq_refl (Zneg Zone)))))

theorem eisConj_respects {z w : EisInt} :
    EisEq z w -> EisEq (eisConj z) (eisConj w) := by
  intro h
  constructor
  · exact zsub_respects h.left h.right
  · exact zlaws.neg_respects h.right

theorem eisConj_involutive (z : EisInt) :
    EisEq (eisConj (eisConj z)) z := by
  constructor
  · exact zsub_sub_neg_right z.re z.om
  · exact zneg_neg z.om

theorem eisConj_mul (z w : EisInt) :
    EisEq (eisConj (eisMul z w))
      (eisMul (eisConj z) (eisConj w)) := by
  constructor
  · exact zlaws.eq_trans
      (zconj_mul_re_left z.re z.om w.re w.om)
      (zlaws.eq_symm (zconj_mul_re_right z.re z.om w.re w.om))
  · exact zlaws.eq_trans
      (zneg_sub (Zadd (Zmul z.re w.om) (Zmul z.om w.re)) (Zmul z.om w.om))
      (zlaws.eq_symm (zconj_mul_om_right z.re z.om w.re w.om))

theorem eisMul_conj_norm (z : EisInt) :
    EisEq (eisMul z (eisConj z)) (eisOfInt (eisNorm z)) := by
  constructor
  · exact zconj_norm_re z.re z.om
  · exact zconj_norm_om z.re z.om

theorem eisConj_mul_self_norm (z : EisInt) :
    EisEq (eisMul (eisConj z) z) (eisOfInt (eisNorm z)) :=
  EisEq_trans (eisMul_comm (eisConj z) z) (eisMul_conj_norm z)

theorem eisOfInt_mul (a b : Z) :
    EisEq (eisMul (eisOfInt a) (eisOfInt b)) (eisOfInt (Zmul a b)) := by
  constructor
  · exact zlaws.eq_trans
      (zsub_respects (zlaws.eq_refl (Zmul a b)) (zlaws.mul_zero Zzero))
      (zlaws.add_zero (Zmul a b))
  · exact zlaws.eq_trans
      (zsub_respects
        (zlaws.eq_trans
          (zlaws.add_respects (zlaws.mul_zero a) (zlaws.zero_mul b))
          (zlaws.add_zero Zzero))
        (zlaws.mul_zero Zzero))
      (zlaws.add_zero Zzero)

theorem eisNorm_respects {z w : EisInt} :
    EisEq z w -> Zeq (eisNorm z) (eisNorm w) := by
  intro h
  exact zlaws.add_respects
    (zsub_respects
      (zlaws.mul_respects h.left h.left)
      (zlaws.mul_respects h.left h.right))
    (zlaws.mul_respects h.right h.right)

theorem eisNorm_mul (z w : EisInt) :
    Zeq (eisNorm (eisMul z w))
      (Zmul (eisNorm z) (eisNorm w)) := by
  let p := eisMul z w
  have productNorm :
      EisEq (eisMul p (eisConj p)) (eisOfInt (eisNorm p)) :=
    eisMul_conj_norm p
  have conjProduct :
      EisEq (eisConj p) (eisMul (eisConj z) (eisConj w)) := by
    exact eisConj_mul z w
  have replaceConj :
      EisEq (eisMul p (eisConj p))
        (eisMul (eisMul z w)
          (eisMul (eisConj z) (eisConj w))) := by
    exact eisMul_respects (EisEq_refl p) conjProduct
  have reassocLeft :
      EisEq (eisMul (eisMul z w)
          (eisMul (eisConj z) (eisConj w)))
        (eisMul z
          (eisMul w (eisMul (eisConj z) (eisConj w)))) :=
    eisMul_assoc z w (eisMul (eisConj z) (eisConj w))
  have moveConjZ :
      EisEq
        (eisMul w (eisMul (eisConj z) (eisConj w)))
        (eisMul (eisConj z) (eisMul w (eisConj w))) := by
    exact EisEq_trans
      (EisEq_symm (eisMul_assoc w (eisConj z) (eisConj w)))
      (EisEq_trans
        (eisMul_respects (eisMul_comm w (eisConj z))
          (EisEq_refl (eisConj w)))
        (eisMul_assoc (eisConj z) w (eisConj w)))
  have reassocRight :
      EisEq
        (eisMul z
          (eisMul (eisConj z) (eisMul w (eisConj w))))
        (eisMul (eisMul z (eisConj z))
          (eisMul w (eisConj w))) :=
    EisEq_symm (eisMul_assoc z (eisConj z)
      (eisMul w (eisConj w)))
  have toNormFactors :
      EisEq
        (eisMul (eisMul z w)
          (eisMul (eisConj z) (eisConj w)))
        (eisMul (eisOfInt (eisNorm z)) (eisOfInt (eisNorm w))) := by
    exact EisEq_trans reassocLeft
      (EisEq_trans (eisMul_respects (EisEq_refl z) moveConjZ)
        (EisEq_trans reassocRight
          (eisMul_respects (eisMul_conj_norm z)
            (eisMul_conj_norm w))))
  have productAsNorm :
      EisEq (eisOfInt (eisNorm p))
        (eisMul (eisOfInt (eisNorm z)) (eisOfInt (eisNorm w))) :=
    EisEq_trans (EisEq_symm productNorm)
      (EisEq_trans replaceConj toNormFactors)
  have productAsInt :
      EisEq (eisMul (eisOfInt (eisNorm z)) (eisOfInt (eisNorm w)))
        (eisOfInt (Zmul (eisNorm z) (eisNorm w))) :=
    eisOfInt_mul (eisNorm z) (eisNorm w)
  exact zlaws.eq_trans productAsNorm.left productAsInt.left

structure EisIntCommRingLaws where
  eq_refl : ∀ z : EisInt, EisEq z z
  eq_symm : ∀ {z w : EisInt}, EisEq z w -> EisEq w z
  eq_trans :
    ∀ {x y z : EisInt}, EisEq x y -> EisEq y z -> EisEq x z
  add_respects :
    ∀ {x x' y y' : EisInt}, EisEq x x' -> EisEq y y' ->
      EisEq (eisAdd x y) (eisAdd x' y')
  mul_respects :
    ∀ {x x' y y' : EisInt}, EisEq x x' -> EisEq y y' ->
      EisEq (eisMul x y) (eisMul x' y')
  neg_respects :
    ∀ {x y : EisInt}, EisEq x y -> EisEq (eisNeg x) (eisNeg y)
  add_comm : ∀ x y : EisInt, EisEq (eisAdd x y) (eisAdd y x)
  add_assoc :
    ∀ x y z : EisInt,
      EisEq (eisAdd (eisAdd x y) z) (eisAdd x (eisAdd y z))
  add_zero : ∀ x : EisInt, EisEq (eisAdd x eisZero) x
  zero_add : ∀ x : EisInt, EisEq (eisAdd eisZero x) x
  add_neg : ∀ x : EisInt, EisEq (eisAdd x (eisNeg x)) eisZero
  neg_add : ∀ x : EisInt, EisEq (eisAdd (eisNeg x) x) eisZero
  mul_comm : ∀ x y : EisInt, EisEq (eisMul x y) (eisMul y x)
  mul_assoc :
    ∀ x y z : EisInt,
      EisEq (eisMul (eisMul x y) z) (eisMul x (eisMul y z))
  mul_one : ∀ x : EisInt, EisEq (eisMul x eisOne) x
  one_mul : ∀ x : EisInt, EisEq (eisMul eisOne x) x
  mul_zero : ∀ x : EisInt, EisEq (eisMul x eisZero) eisZero
  zero_mul : ∀ x : EisInt, EisEq (eisMul eisZero x) eisZero
  left_distrib :
    ∀ x y z : EisInt,
      EisEq (eisMul x (eisAdd y z))
        (eisAdd (eisMul x y) (eisMul x z))
  right_distrib :
    ∀ x y z : EisInt,
      EisEq (eisMul (eisAdd x y) z)
        (eisAdd (eisMul x z) (eisMul y z))

def EisInt_comm_ring_laws : EisIntCommRingLaws where
  eq_refl := EisEq_refl
  eq_symm := by
    intro z w
    exact EisEq_symm
  eq_trans := by
    intro x y z
    exact EisEq_trans
  add_respects := by
    intro x x' y y'
    exact eisAdd_respects
  mul_respects := by
    intro x x' y y'
    exact eisMul_respects
  neg_respects := by
    intro x y
    exact eisNeg_respects
  add_comm := eisAdd_comm
  add_assoc := eisAdd_assoc
  add_zero := eisAdd_zero
  zero_add := eisAdd_zero_left
  add_neg := eisAdd_neg
  neg_add := eisAdd_neg_left
  mul_comm := eisMul_comm
  mul_assoc := eisMul_assoc
  mul_one := eisMul_one
  one_mul := eisMul_one_left
  mul_zero := eisMul_zero
  zero_mul := eisMul_zero_left
  left_distrib := eisMul_add_distrib
  right_distrib := eisMul_add_distrib_right

end BEDC.Derived.EisensteinUp
