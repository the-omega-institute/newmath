import BEDC.Derived.IntUp.CommRing

namespace BEDC.Derived.PowerSeriesUp

abbrev IntegerUp := BEDC.Derived.PrimeUp.IntegerUp
abbrev PSeries := Nat -> IntegerUp

private abbrev coeffZero : IntegerUp :=
  BEDC.Derived.RationalUp.intZero

private abbrev coeffOne : IntegerUp :=
  BEDC.Derived.RationalUp.intOne

private abbrev coeffAdd : IntegerUp -> IntegerUp -> IntegerUp :=
  BEDC.Derived.RationalUp.IntAdd

private abbrev coeffMul : IntegerUp -> IntegerUp -> IntegerUp :=
  BEDC.Derived.RationalUp.IntMul

private abbrev coeffNeg : IntegerUp -> IntegerUp :=
  BEDC.Derived.RationalUp.IntNeg

private abbrev coeffEq : IntegerUp -> IntegerUp -> Prop :=
  BEDC.Derived.RationalUp.IntEq

private abbrev intLaws : BEDC.Derived.IntUp.IntegerUpCommRingLaws :=
  BEDC.Derived.IntUp.IntegerUp_comm_ring_laws

def psCoeff (p : PSeries) (n : Nat) : IntegerUp :=
  p n

def PSEq (p q : PSeries) : Prop :=
  forall n : Nat, coeffEq (psCoeff p n) (psCoeff q n)

def psZero : PSeries :=
  fun _ => coeffZero

def psOne : PSeries
  | 0 => coeffOne
  | Nat.succ _ => coeffZero

def psAdd (p q : PSeries) : PSeries :=
  fun n => coeffAdd (p n) (q n)

def psNeg (p : PSeries) : PSeries :=
  fun n => coeffNeg (p n)

def psTail (p : PSeries) : PSeries :=
  fun n => p (Nat.succ n)

def psScale (a : IntegerUp) (p : PSeries) : PSeries :=
  fun n => coeffMul a (p n)

def psShift (p : PSeries) : PSeries
  | 0 => coeffZero
  | Nat.succ n => p n

def psMul (p q : PSeries) : PSeries
  | 0 => coeffMul (p 0) (q 0)
  | Nat.succ n => coeffAdd (coeffMul (p 0) (q (Nat.succ n))) (psMul (psTail p) q n)

def psConvAt (p q : PSeries) : Nat -> IntegerUp :=
  psMul p q

theorem PSEq_refl (p : PSeries) : PSEq p p := by
  intro n
  exact intLaws.eq_refl (p n)

theorem PSEq_symm {p q : PSeries} : PSEq p q -> PSEq q p := by
  intro same n
  exact intLaws.eq_symm (same n)

theorem PSEq_trans {p q r : PSeries} : PSEq p q -> PSEq q r -> PSEq p r := by
  intro pq qr n
  exact intLaws.eq_trans (pq n) (qr n)

theorem psTail_respects {p q : PSeries} :
    PSEq p q -> PSEq (psTail p) (psTail q) := by
  intro pq n
  exact pq (Nat.succ n)

theorem psAdd_respects {p p' q q' : PSeries} :
    PSEq p p' -> PSEq q q' -> PSEq (psAdd p q) (psAdd p' q') := by
  intro pp' qq' n
  exact intLaws.add_respects (pp' n) (qq' n)

theorem psNeg_respects {p q : PSeries} :
    PSEq p q -> PSEq (psNeg p) (psNeg q) := by
  intro pq n
  exact intLaws.neg_respects (pq n)

theorem psScale_respects {a b : IntegerUp} {p q : PSeries} :
    coeffEq a b -> PSEq p q -> PSEq (psScale a p) (psScale b q) := by
  intro ab pq n
  exact intLaws.mul_respects ab (pq n)

theorem psShift_respects {p q : PSeries} :
    PSEq p q -> PSEq (psShift p) (psShift q) := by
  intro pq n
  cases n with
  | zero =>
      exact intLaws.eq_refl coeffZero
  | succ n =>
      exact pq n

theorem psTail_scale (a : IntegerUp) (p : PSeries) :
    PSEq (psTail (psScale a p)) (psScale a (psTail p)) := by
  intro n
  exact intLaws.eq_refl (coeffMul a (p (Nat.succ n)))

theorem psTail_one_zero : PSEq (psTail psOne) psZero := by
  intro n
  exact intLaws.eq_refl coeffZero

theorem psMul_respects {p p' q q' : PSeries} :
    PSEq p p' -> PSEq q q' -> PSEq (psMul p q) (psMul p' q') := by
  intro pp' qq' n
  induction n generalizing p p' q q' with
  | zero =>
      exact intLaws.mul_respects (pp' 0) (qq' 0)
  | succ n ih =>
      exact intLaws.add_respects
        (intLaws.mul_respects (pp' 0) (qq' (Nat.succ n)))
        (ih (psTail_respects pp') qq')

theorem psAdd_comm (p q : PSeries) :
    PSEq (psAdd p q) (psAdd q p) := by
  intro n
  exact intLaws.add_comm (p n) (q n)

theorem psAdd_assoc (p q r : PSeries) :
    PSEq (psAdd (psAdd p q) r) (psAdd p (psAdd q r)) := by
  intro n
  exact intLaws.add_assoc (p n) (q n) (r n)

theorem psAdd_zero (p : PSeries) :
    PSEq (psAdd p psZero) p := by
  intro n
  exact intLaws.add_zero (p n)

theorem psAdd_zero_left (p : PSeries) :
    PSEq (psAdd psZero p) p := by
  intro n
  exact intLaws.zero_add (p n)

theorem psAdd_neg (p : PSeries) :
    PSEq (psAdd p (psNeg p)) psZero := by
  intro n
  exact intLaws.add_neg (p n)

theorem psAdd_neg_left (p : PSeries) :
    PSEq (psAdd (psNeg p) p) psZero := by
  intro n
  exact intLaws.neg_add (p n)

private theorem coeffAdd_right_swap (a b c : IntegerUp) :
    coeffEq (coeffAdd a (coeffAdd b c)) (coeffAdd b (coeffAdd a c)) :=
  intLaws.eq_trans (intLaws.eq_symm (intLaws.add_assoc a b c))
    (intLaws.eq_trans
      (intLaws.add_respects (intLaws.add_comm a b) (intLaws.eq_refl c))
      (intLaws.add_assoc b a c))

private theorem coeffAdd_four_swap (a b c d : IntegerUp) :
    coeffEq (coeffAdd (coeffAdd a b) (coeffAdd c d))
      (coeffAdd (coeffAdd a c) (coeffAdd b d)) :=
  intLaws.eq_trans (intLaws.add_assoc a b (coeffAdd c d))
    (intLaws.eq_trans
      (intLaws.add_respects (intLaws.eq_refl a) (coeffAdd_right_swap b c d))
      (intLaws.eq_symm (intLaws.add_assoc a c (coeffAdd b d))))

private theorem coeffMul_assoc_distrib_tail
    (a b c t u : IntegerUp) :
    coeffEq (coeffAdd (coeffMul (coeffMul a b) c) (coeffAdd (coeffMul a t) u))
      (coeffAdd (coeffMul a (coeffAdd (coeffMul b c) t)) u) :=
  intLaws.eq_trans
    (intLaws.add_respects (intLaws.mul_assoc a b c) (intLaws.eq_refl (coeffAdd (coeffMul a t) u)))
    (intLaws.eq_trans
      (intLaws.eq_symm (intLaws.add_assoc (coeffMul a (coeffMul b c)) (coeffMul a t) u))
      (intLaws.add_respects
        (intLaws.eq_symm (intLaws.left_distrib a (coeffMul b c) t))
        (intLaws.eq_refl u)))

theorem psMul_zero (p : PSeries) :
    PSEq (psMul p psZero) psZero := by
  intro n
  induction n generalizing p with
  | zero =>
      exact intLaws.mul_zero (p 0)
  | succ n ih =>
      exact intLaws.eq_trans
        (intLaws.add_respects (intLaws.mul_zero (p 0)) (ih (psTail p)))
        (intLaws.zero_add coeffZero)

theorem psMul_zero_left (p : PSeries) :
    PSEq (psMul psZero p) psZero := by
  intro n
  induction n generalizing p with
  | zero =>
      exact intLaws.zero_mul (p 0)
  | succ n ih =>
      exact intLaws.eq_trans
        (intLaws.add_respects (intLaws.zero_mul (p (Nat.succ n))) (ih p))
        (intLaws.zero_add coeffZero)

theorem psMul_one_left (p : PSeries) :
    PSEq (psMul psOne p) p := by
  intro n
  cases n with
  | zero =>
      exact intLaws.one_mul (p 0)
  | succ n =>
      have tailProductZero :
          coeffEq (psMul (psTail psOne) p n) coeffZero :=
        intLaws.eq_trans
          ((psMul_respects psTail_one_zero (PSEq_refl p)) n)
          (psMul_zero_left p n)
      exact intLaws.eq_trans
        (intLaws.add_respects (intLaws.one_mul (p (Nat.succ n))) tailProductZero)
        (intLaws.add_zero (p (Nat.succ n)))

theorem psMul_succ_right (p q : PSeries) (n : Nat) :
    coeffEq (psMul p q (Nat.succ n))
      (coeffAdd (psMul p (psTail q) n) (coeffMul (p (Nat.succ n)) (q 0))) := by
  induction n generalizing p q with
  | zero =>
      exact intLaws.eq_refl
        (coeffAdd (coeffMul (p 0) (q 1)) (coeffMul (p 1) (q 0)))
  | succ n ih =>
      exact intLaws.eq_trans
        (intLaws.add_respects
          (intLaws.eq_refl (coeffMul (p 0) (q (Nat.succ (Nat.succ n)))))
          (ih (psTail p) q))
        (intLaws.eq_symm
          (intLaws.add_assoc
            (coeffMul (p 0) (q (Nat.succ (Nat.succ n))))
            (psMul (psTail p) (psTail q) n)
            (coeffMul (p (Nat.succ (Nat.succ n))) (q 0))))

theorem psMul_comm (p q : PSeries) :
    PSEq (psMul p q) (psMul q p) := by
  intro n
  induction n generalizing p q with
  | zero =>
      exact intLaws.mul_comm (p 0) (q 0)
  | succ n ih =>
      have tailComm : coeffEq (psMul (psTail p) q n) (psMul q (psTail p) n) :=
        ih (psTail p) q
      have headComm :
          coeffEq (coeffMul (p 0) (q (Nat.succ n)))
            (coeffMul (q (Nat.succ n)) (p 0)) :=
        intLaws.mul_comm (p 0) (q (Nat.succ n))
      have align :
          coeffEq
            (coeffAdd (coeffMul (p 0) (q (Nat.succ n))) (psMul (psTail p) q n))
            (coeffAdd (psMul q (psTail p) n) (coeffMul (q (Nat.succ n)) (p 0))) :=
        intLaws.eq_trans
          (intLaws.add_respects headComm tailComm)
          (intLaws.add_comm (coeffMul (q (Nat.succ n)) (p 0)) (psMul q (psTail p) n))
      exact intLaws.eq_trans align (intLaws.eq_symm (psMul_succ_right q p n))

theorem psMul_one (p : PSeries) :
    PSEq (psMul p psOne) p := by
  exact PSEq_trans (psMul_comm p psOne) (psMul_one_left p)

theorem psMul_add_distrib (p q r : PSeries) :
    PSEq (psMul p (psAdd q r)) (psAdd (psMul p q) (psMul p r)) := by
  intro n
  induction n generalizing p q r with
  | zero =>
      exact intLaws.left_distrib (p 0) (q 0) (r 0)
  | succ n ih =>
      have tailDistrib :
          coeffEq (psMul (psTail p) (psAdd q r) n)
            (coeffAdd (psMul (psTail p) q n) (psMul (psTail p) r n)) :=
        ih (psTail p) q r
      have expanded :
          coeffEq
            (coeffAdd (coeffMul (p 0) (coeffAdd (q (Nat.succ n)) (r (Nat.succ n))))
              (psMul (psTail p) (psAdd q r) n))
            (coeffAdd (coeffAdd (coeffMul (p 0) (q (Nat.succ n)))
              (coeffMul (p 0) (r (Nat.succ n))))
              (coeffAdd (psMul (psTail p) q n) (psMul (psTail p) r n))) :=
        intLaws.add_respects
          (intLaws.left_distrib (p 0) (q (Nat.succ n)) (r (Nat.succ n)))
          tailDistrib
      exact intLaws.eq_trans expanded
        (coeffAdd_four_swap
          (coeffMul (p 0) (q (Nat.succ n)))
          (coeffMul (p 0) (r (Nat.succ n)))
          (psMul (psTail p) q n)
          (psMul (psTail p) r n))

theorem psMul_add_distrib_right (p q r : PSeries) :
    PSEq (psMul (psAdd p q) r) (psAdd (psMul p r) (psMul q r)) := by
  exact PSEq_trans (psMul_comm (psAdd p q) r)
    (PSEq_trans (psMul_add_distrib r p q)
      (psAdd_respects (psMul_comm r p) (psMul_comm r q)))

theorem psMul_decompose (p q : PSeries) :
    PSEq (psMul p q)
      (psAdd (psScale (p 0) q) (psShift (psMul (psTail p) q))) := by
  intro n
  cases n with
  | zero =>
      exact intLaws.eq_symm (intLaws.add_zero (coeffMul (p 0) (q 0)))
  | succ n =>
      exact intLaws.eq_refl
        (coeffAdd (coeffMul (p 0) (q (Nat.succ n))) (psMul (psTail p) q n))

theorem psTail_mul (p q : PSeries) :
    PSEq (psTail (psMul p q))
      (psAdd (psScale (p 0) (psTail q)) (psMul (psTail p) q)) := by
  intro n
  exact intLaws.eq_refl
    (coeffAdd (coeffMul (p 0) (q (Nat.succ n))) (psMul (psTail p) q n))

theorem psScale_mul_left (a : IntegerUp) (p q : PSeries) :
    PSEq (psMul (psScale a p) q) (psScale a (psMul p q)) := by
  intro n
  induction n generalizing p q with
  | zero =>
      exact intLaws.mul_assoc a (p 0) (q 0)
  | succ n ih =>
      have tailProduct :
          coeffEq (psMul (psTail (psScale a p)) q n)
            (coeffMul a (psMul (psTail p) q n)) :=
        intLaws.eq_trans
          ((psMul_respects (psTail_scale a p) (PSEq_refl q)) n)
          (ih (psTail p) q)
      have headAssoc :
          coeffEq (coeffMul (coeffMul a (p 0)) (q (Nat.succ n)))
            (coeffMul a (coeffMul (p 0) (q (Nat.succ n)))) :=
        intLaws.mul_assoc a (p 0) (q (Nat.succ n))
      exact intLaws.eq_trans
        (intLaws.add_respects headAssoc tailProduct)
        (intLaws.eq_symm
          (intLaws.left_distrib a (coeffMul (p 0) (q (Nat.succ n)))
            (psMul (psTail p) q n)))

theorem psShift_mul_left (p q : PSeries) :
    PSEq (psMul (psShift p) q) (psShift (psMul p q)) := by
  intro n
  cases n with
  | zero =>
      exact intLaws.zero_mul (q 0)
  | succ n =>
      exact intLaws.eq_trans
        (intLaws.add_respects (intLaws.zero_mul (q (Nat.succ n)))
          (intLaws.eq_refl (psMul p q n)))
        (intLaws.zero_add (psMul p q n))

theorem psMul_assoc (p q r : PSeries) :
    PSEq (psMul (psMul p q) r) (psMul p (psMul q r)) := by
  intro n
  induction n generalizing p q r with
  | zero =>
      exact intLaws.mul_assoc (p 0) (q 0) (r 0)
  | succ n ih =>
      have headAssoc :
          coeffEq (coeffMul (psMul p q 0) (r (Nat.succ n)))
            (coeffMul (coeffMul (p 0) (q 0)) (r (Nat.succ n))) :=
        intLaws.eq_refl (coeffMul (coeffMul (p 0) (q 0)) (r (Nat.succ n)))
      have tailDecomp :
          coeffEq (psMul (psTail (psMul p q)) r n)
            (psMul (psAdd (psScale (p 0) (psTail q)) (psMul (psTail p) q)) r n) :=
        (psMul_respects (psTail_mul p q) (PSEq_refl r)) n
      have rightDistrib :
          coeffEq
            (psMul (psAdd (psScale (p 0) (psTail q)) (psMul (psTail p) q)) r n)
            (coeffAdd
              (psMul (psScale (p 0) (psTail q)) r n)
              (psMul (psMul (psTail p) q) r n)) :=
        psMul_add_distrib_right (psScale (p 0) (psTail q)) (psMul (psTail p) q) r n
      have scaled :
          coeffEq (psMul (psScale (p 0) (psTail q)) r n)
            (coeffMul (p 0) (psMul (psTail q) r n)) :=
        psScale_mul_left (p 0) (psTail q) r n
      have tailAssoc :
          coeffEq (psMul (psMul (psTail p) q) r n)
            (psMul (psTail p) (psMul q r) n) :=
        ih (psTail p) q r
      have tailNorm :
          coeffEq (psMul (psTail (psMul p q)) r n)
            (coeffAdd (coeffMul (p 0) (psMul (psTail q) r n))
              (psMul (psTail p) (psMul q r) n)) :=
        intLaws.eq_trans tailDecomp
          (intLaws.eq_trans rightDistrib (intLaws.add_respects scaled tailAssoc))
      have leftNorm :
          coeffEq
            (coeffAdd (coeffMul (psMul p q 0) (r (Nat.succ n)))
              (psMul (psTail (psMul p q)) r n))
            (coeffAdd (coeffMul (coeffMul (p 0) (q 0)) (r (Nat.succ n)))
              (coeffAdd (coeffMul (p 0) (psMul (psTail q) r n))
                (psMul (psTail p) (psMul q r) n))) :=
        intLaws.add_respects headAssoc tailNorm
      exact intLaws.eq_trans leftNorm
        (coeffMul_assoc_distrib_tail (p 0) (q 0) (r (Nat.succ n))
          (psMul (psTail q) r n) (psMul (psTail p) (psMul q r) n))

structure PowerSeriesCommRingLaws where
  eq_refl : forall p : PSeries, PSEq p p
  eq_symm : forall {p q : PSeries}, PSEq p q -> PSEq q p
  eq_trans : forall {p q r : PSeries}, PSEq p q -> PSEq q r -> PSEq p r
  add_respects :
    forall {p p' q q' : PSeries}, PSEq p p' -> PSEq q q' ->
      PSEq (psAdd p q) (psAdd p' q')
  mul_respects :
    forall {p p' q q' : PSeries}, PSEq p p' -> PSEq q q' ->
      PSEq (psMul p q) (psMul p' q')
  neg_respects : forall {p q : PSeries}, PSEq p q -> PSEq (psNeg p) (psNeg q)
  add_comm : forall p q : PSeries, PSEq (psAdd p q) (psAdd q p)
  add_assoc :
    forall p q r : PSeries,
      PSEq (psAdd (psAdd p q) r) (psAdd p (psAdd q r))
  add_zero : forall p : PSeries, PSEq (psAdd p psZero) p
  zero_add : forall p : PSeries, PSEq (psAdd psZero p) p
  add_neg : forall p : PSeries, PSEq (psAdd p (psNeg p)) psZero
  neg_add : forall p : PSeries, PSEq (psAdd (psNeg p) p) psZero
  mul_comm : forall p q : PSeries, PSEq (psMul p q) (psMul q p)
  mul_assoc :
    forall p q r : PSeries,
      PSEq (psMul (psMul p q) r) (psMul p (psMul q r))
  mul_one : forall p : PSeries, PSEq (psMul p psOne) p
  one_mul : forall p : PSeries, PSEq (psMul psOne p) p
  mul_zero : forall p : PSeries, PSEq (psMul p psZero) psZero
  zero_mul : forall p : PSeries, PSEq (psMul psZero p) psZero
  left_distrib :
    forall p q r : PSeries,
      PSEq (psMul p (psAdd q r))
        (psAdd (psMul p q) (psMul p r))
  right_distrib :
    forall p q r : PSeries,
      PSEq (psMul (psAdd p q) r)
        (psAdd (psMul p r) (psMul q r))

def power_series_comm_ring_laws : PowerSeriesCommRingLaws where
  eq_refl := PSEq_refl
  eq_symm := by
    intro p q
    exact PSEq_symm
  eq_trans := by
    intro p q r
    exact PSEq_trans
  add_respects := by
    intro p p' q q'
    exact psAdd_respects
  mul_respects := by
    intro p p' q q'
    exact psMul_respects
  neg_respects := by
    intro p q
    exact psNeg_respects
  add_comm := psAdd_comm
  add_assoc := psAdd_assoc
  add_zero := psAdd_zero
  zero_add := psAdd_zero_left
  add_neg := psAdd_neg
  neg_add := psAdd_neg_left
  mul_comm := psMul_comm
  mul_assoc := psMul_assoc
  mul_one := psMul_one
  one_mul := psMul_one_left
  mul_zero := psMul_zero
  zero_mul := psMul_zero_left
  left_distrib := psMul_add_distrib
  right_distrib := psMul_add_distrib_right

end BEDC.Derived.PowerSeriesUp
