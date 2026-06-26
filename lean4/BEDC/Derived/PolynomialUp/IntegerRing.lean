import BEDC.Derived.IntUp.Arithmetic
import BEDC.Derived.IntUp.CommRing

namespace BEDC.Derived.PolynomialUp

abbrev IntegerUp := BEDC.Derived.PrimeUp.IntegerUp
abbrev Poly := List IntegerUp

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

def polyZero : Poly := []

def polyOne : Poly := [coeffOne]

def polyCoeff : Poly -> Nat -> IntegerUp
  | [], _ => coeffZero
  | a :: _, 0 => a
  | _ :: as, Nat.succ n => polyCoeff as n

def PolyEq (p q : Poly) : Prop :=
  forall n : Nat, coeffEq (polyCoeff p n) (polyCoeff q n)

def polyAdd : Poly -> Poly -> Poly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => coeffAdd a b :: polyAdd p q

def polyNeg : Poly -> Poly
  | [] => []
  | a :: p => coeffNeg a :: polyNeg p

def polyScale (a : IntegerUp) : Poly -> Poly
  | [] => []
  | b :: q => coeffMul a b :: polyScale a q

def polyShift : Poly -> Poly
  | [] => []
  | a :: p => coeffZero :: a :: p

def polyMul : Poly -> Poly -> Poly
  | [], _ => []
  | a :: p, q => polyAdd (polyScale a q) (polyShift (polyMul p q))

def polyEval (x : IntegerUp) : Poly -> IntegerUp
  | [] => coeffZero
  | a :: p => coeffAdd a (coeffMul x (polyEval x p))

def coeffOfNat (n : Nat) : IntegerUp :=
  BEDC.Derived.RationalUp.intOfNat
    (BEDC.Derived.IntUp.natToUnary n)
    (BEDC.Derived.IntUp.natToUnary_unary n)

def polyDerivFrom : Nat -> Poly -> Poly
  | _, [] => []
  | n, a :: p => coeffMul (coeffOfNat n) a :: polyDerivFrom (Nat.succ n) p

def polyDeriv : Poly -> Poly
  | [] => []
  | _ :: p => polyDerivFrom 1 p

theorem PolyEq_refl (p : Poly) : PolyEq p p := by
  intro n
  exact intLaws.eq_refl (polyCoeff p n)

theorem PolyEq_symm {p q : Poly} : PolyEq p q -> PolyEq q p := by
  intro same n
  exact intLaws.eq_symm (same n)

theorem PolyEq_trans {p q r : Poly} : PolyEq p q -> PolyEq q r -> PolyEq p r := by
  intro pq qr n
  exact intLaws.eq_trans (pq n) (qr n)

private theorem coeffNeg_zero :
    coeffEq coeffZero (coeffNeg coeffZero) := by
  exact intLaws.eq_trans (intLaws.eq_symm (intLaws.add_neg coeffZero))
    (intLaws.zero_add (coeffNeg coeffZero))

theorem polyCoeff_add (p q : Poly) (n : Nat) :
    coeffEq (polyCoeff (polyAdd p q) n)
      (coeffAdd (polyCoeff p n) (polyCoeff q n)) := by
  induction p generalizing q n with
  | nil =>
      cases q with
      | nil =>
          exact intLaws.eq_symm (intLaws.zero_add coeffZero)
      | cons b q =>
          cases n with
          | zero =>
              exact intLaws.eq_symm (intLaws.zero_add b)
          | succ n =>
              exact intLaws.eq_symm (intLaws.zero_add (polyCoeff q n))
  | cons a p ih =>
      cases q with
      | nil =>
          cases n with
          | zero =>
              exact intLaws.eq_symm (intLaws.add_zero a)
          | succ n =>
              exact intLaws.eq_symm (intLaws.add_zero (polyCoeff p n))
      | cons b q =>
          cases n with
          | zero =>
              exact intLaws.eq_refl (coeffAdd a b)
          | succ n =>
              exact ih q n

theorem polyCoeff_neg (p : Poly) (n : Nat) :
    coeffEq (polyCoeff (polyNeg p) n) (coeffNeg (polyCoeff p n)) := by
  induction p generalizing n with
  | nil =>
      exact coeffNeg_zero
  | cons a p ih =>
      cases n with
      | zero =>
          exact intLaws.eq_refl (coeffNeg a)
      | succ n =>
          exact ih n

theorem polyCoeff_scale (a : IntegerUp) (p : Poly) (n : Nat) :
    coeffEq (polyCoeff (polyScale a p) n) (coeffMul a (polyCoeff p n)) := by
  induction p generalizing n with
  | nil =>
      exact intLaws.eq_symm (intLaws.mul_zero a)
  | cons b p ih =>
      cases n with
      | zero =>
          exact intLaws.eq_refl (coeffMul a b)
      | succ n =>
          exact ih n

theorem polyCoeff_shift_zero (p : Poly) :
    coeffEq (polyCoeff (polyShift p) 0) coeffZero := by
  cases p with
  | nil =>
      exact intLaws.eq_refl coeffZero
  | cons _ _ =>
      exact intLaws.eq_refl coeffZero

theorem polyCoeff_shift_succ (p : Poly) (n : Nat) :
    coeffEq (polyCoeff (polyShift p) (Nat.succ n)) (polyCoeff p n) := by
  cases p with
  | nil =>
      exact intLaws.eq_refl coeffZero
  | cons _ _ =>
      exact intLaws.eq_refl (polyCoeff _ n)

theorem polyAdd_respects {p p' q q' : Poly} :
    PolyEq p p' -> PolyEq q q' -> PolyEq (polyAdd p q) (polyAdd p' q') := by
  intro pp' qq' n
  exact intLaws.eq_trans (polyCoeff_add p q n)
    (intLaws.eq_trans
      (intLaws.add_respects (pp' n) (qq' n))
      (intLaws.eq_symm (polyCoeff_add p' q' n)))

theorem polyNeg_respects {p q : Poly} :
    PolyEq p q -> PolyEq (polyNeg p) (polyNeg q) := by
  intro pq n
  exact intLaws.eq_trans (polyCoeff_neg p n)
    (intLaws.eq_trans (intLaws.neg_respects (pq n))
      (intLaws.eq_symm (polyCoeff_neg q n)))

theorem polyScale_respects {a b : IntegerUp} {p q : Poly} :
    coeffEq a b -> PolyEq p q -> PolyEq (polyScale a p) (polyScale b q) := by
  intro ab pq n
  exact intLaws.eq_trans (polyCoeff_scale a p n)
    (intLaws.eq_trans (intLaws.mul_respects ab (pq n))
      (intLaws.eq_symm (polyCoeff_scale b q n)))

theorem polyShift_respects {p q : Poly} :
    PolyEq p q -> PolyEq (polyShift p) (polyShift q) := by
  intro pq n
  cases n with
  | zero =>
      exact intLaws.eq_trans (polyCoeff_shift_zero p)
        (intLaws.eq_symm (polyCoeff_shift_zero q))
  | succ n =>
      exact intLaws.eq_trans (polyCoeff_shift_succ p n)
        (intLaws.eq_trans (pq n) (intLaws.eq_symm (polyCoeff_shift_succ q n)))

theorem polyAdd_comm (p q : Poly) :
    PolyEq (polyAdd p q) (polyAdd q p) := by
  intro n
  exact intLaws.eq_trans (polyCoeff_add p q n)
    (intLaws.eq_trans (intLaws.add_comm (polyCoeff p n) (polyCoeff q n))
      (intLaws.eq_symm (polyCoeff_add q p n)))

theorem polyAdd_assoc (p q r : Poly) :
    PolyEq (polyAdd (polyAdd p q) r) (polyAdd p (polyAdd q r)) := by
  intro n
  exact intLaws.eq_trans (polyCoeff_add (polyAdd p q) r n)
    (intLaws.eq_trans
      (intLaws.add_respects (polyCoeff_add p q n) (intLaws.eq_refl (polyCoeff r n)))
      (intLaws.eq_trans
        (intLaws.add_assoc (polyCoeff p n) (polyCoeff q n) (polyCoeff r n))
        (intLaws.eq_trans
          (intLaws.add_respects (intLaws.eq_refl (polyCoeff p n))
            (intLaws.eq_symm (polyCoeff_add q r n)))
          (intLaws.eq_symm (polyCoeff_add p (polyAdd q r) n)))))

theorem polyAdd_zero (p : Poly) :
    PolyEq (polyAdd p polyZero) p := by
  intro n
  exact intLaws.eq_trans (polyCoeff_add p polyZero n)
    (intLaws.add_zero (polyCoeff p n))

theorem polyAdd_zero_left (p : Poly) :
    PolyEq (polyAdd polyZero p) p := by
  intro n
  exact intLaws.eq_trans (polyCoeff_add polyZero p n)
    (intLaws.zero_add (polyCoeff p n))

theorem polyAdd_neg (p : Poly) :
    PolyEq (polyAdd p (polyNeg p)) polyZero := by
  intro n
  exact intLaws.eq_trans (polyCoeff_add p (polyNeg p) n)
    (intLaws.eq_trans
      (intLaws.add_respects (intLaws.eq_refl (polyCoeff p n)) (polyCoeff_neg p n))
      (intLaws.add_neg (polyCoeff p n)))

theorem polyAdd_neg_left (p : Poly) :
    PolyEq (polyAdd (polyNeg p) p) polyZero := by
  exact PolyEq_trans (polyAdd_comm (polyNeg p) p) (polyAdd_neg p)

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

theorem polyAdd_left_zero_of_eqv {p q : Poly} :
    PolyEq p polyZero -> PolyEq (polyAdd p q) q := by
  intro pZero n
  exact intLaws.eq_trans (polyCoeff_add p q n)
    (intLaws.eq_trans
      (intLaws.add_respects (pZero n) (intLaws.eq_refl (polyCoeff q n)))
      (intLaws.zero_add (polyCoeff q n)))

theorem polyAdd_right_zero_of_eqv {p q : Poly} :
    PolyEq q polyZero -> PolyEq (polyAdd p q) p := by
  intro qZero n
  exact intLaws.eq_trans (polyCoeff_add p q n)
    (intLaws.eq_trans
      (intLaws.add_respects (intLaws.eq_refl (polyCoeff p n)) (qZero n))
      (intLaws.add_zero (polyCoeff p n)))

theorem polyShift_zero_of_eqv {p : Poly} :
    PolyEq p polyZero -> PolyEq (polyShift p) polyZero := by
  intro pZero n
  cases n with
  | zero =>
      exact polyCoeff_shift_zero p
  | succ n =>
      exact intLaws.eq_trans (polyCoeff_shift_succ p n) (pZero n)

theorem polyScale_zero_left (p : Poly) :
    PolyEq (polyScale coeffZero p) polyZero := by
  intro n
  exact intLaws.eq_trans (polyCoeff_scale coeffZero p n)
    (intLaws.zero_mul (polyCoeff p n))

theorem polyScale_one_left (p : Poly) :
    PolyEq (polyScale coeffOne p) p := by
  intro n
  exact intLaws.eq_trans (polyCoeff_scale coeffOne p n)
    (intLaws.one_mul (polyCoeff p n))

theorem polyScale_add (a : IntegerUp) (p q : Poly) :
    PolyEq (polyScale a (polyAdd p q))
      (polyAdd (polyScale a p) (polyScale a q)) := by
  intro n
  exact intLaws.eq_trans (polyCoeff_scale a (polyAdd p q) n)
    (intLaws.eq_trans
      (intLaws.mul_respects (intLaws.eq_refl a) (polyCoeff_add p q n))
      (intLaws.eq_trans
        (intLaws.left_distrib a (polyCoeff p n) (polyCoeff q n))
        (intLaws.eq_symm
          (intLaws.eq_trans (polyCoeff_add (polyScale a p) (polyScale a q) n)
            (intLaws.add_respects
              (polyCoeff_scale a p n) (polyCoeff_scale a q n))))))

theorem polyScale_scale (a b : IntegerUp) (p : Poly) :
    PolyEq (polyScale (coeffMul a b) p) (polyScale a (polyScale b p)) := by
  intro n
  exact intLaws.eq_trans (polyCoeff_scale (coeffMul a b) p n)
    (intLaws.eq_trans
      (intLaws.mul_assoc a b (polyCoeff p n))
      (intLaws.eq_symm
        (intLaws.eq_trans (polyCoeff_scale a (polyScale b p) n)
          (intLaws.mul_respects (intLaws.eq_refl a) (polyCoeff_scale b p n)))))

theorem polyScale_shift (a : IntegerUp) (p : Poly) :
    PolyEq (polyScale a (polyShift p)) (polyShift (polyScale a p)) := by
  intro n
  cases n with
  | zero =>
      exact intLaws.eq_trans (polyCoeff_scale a (polyShift p) 0)
        (intLaws.eq_trans
          (intLaws.mul_respects (intLaws.eq_refl a) (polyCoeff_shift_zero p))
          (intLaws.eq_trans (intLaws.mul_zero a)
            (intLaws.eq_symm (polyCoeff_shift_zero (polyScale a p)))))
  | succ n =>
      exact intLaws.eq_trans (polyCoeff_scale a (polyShift p) (Nat.succ n))
        (intLaws.eq_trans
          (intLaws.mul_respects (intLaws.eq_refl a) (polyCoeff_shift_succ p n))
          (intLaws.eq_trans
            (intLaws.eq_symm (polyCoeff_scale a p n))
            (intLaws.eq_symm (polyCoeff_shift_succ (polyScale a p) n))))

theorem polyAdd_four_swap (p q r s : Poly) :
    PolyEq (polyAdd (polyAdd p q) (polyAdd r s))
      (polyAdd (polyAdd p r) (polyAdd q s)) := by
  intro n
  exact intLaws.eq_trans (polyCoeff_add (polyAdd p q) (polyAdd r s) n)
    (intLaws.eq_trans
      (intLaws.add_respects (polyCoeff_add p q n) (polyCoeff_add r s n))
      (intLaws.eq_trans
        (coeffAdd_four_swap (polyCoeff p n) (polyCoeff q n)
          (polyCoeff r n) (polyCoeff s n))
        (intLaws.eq_trans
          (intLaws.add_respects
            (intLaws.eq_symm (polyCoeff_add p r n))
            (intLaws.eq_symm (polyCoeff_add q s n)))
          (intLaws.eq_symm (polyCoeff_add (polyAdd p r) (polyAdd q s) n)))))

theorem polyShift_add (p q : Poly) :
    PolyEq (polyShift (polyAdd p q)) (polyAdd (polyShift p) (polyShift q)) := by
  intro n
  cases n with
  | zero =>
      exact intLaws.eq_trans (polyCoeff_shift_zero (polyAdd p q))
        (intLaws.eq_symm
          (intLaws.eq_trans (polyCoeff_add (polyShift p) (polyShift q) 0)
            (intLaws.add_respects
              (polyCoeff_shift_zero p) (polyCoeff_shift_zero q))))
  | succ n =>
      exact intLaws.eq_trans (polyCoeff_shift_succ (polyAdd p q) n)
        (intLaws.eq_trans (polyCoeff_add p q n)
          (intLaws.eq_symm
            (intLaws.eq_trans (polyCoeff_add (polyShift p) (polyShift q) (Nat.succ n))
              (intLaws.add_respects
                (polyCoeff_shift_succ p n) (polyCoeff_shift_succ q n)))))

theorem polyMul_zero (p : Poly) :
    PolyEq (polyMul p polyZero) polyZero := by
  induction p with
  | nil =>
      exact PolyEq_refl polyZero
  | cons a p ih =>
      have leftZero :
          PolyEq
            (polyAdd (polyScale a polyZero)
              (polyShift (polyMul p polyZero)))
            (polyShift (polyMul p polyZero)) :=
        polyAdd_left_zero_of_eqv
          (p := polyScale a polyZero)
          (q := polyShift (polyMul p polyZero))
          (polyScale_zero_left polyZero)
      exact PolyEq_trans leftZero (polyShift_zero_of_eqv ih)

theorem polyMul_zero_left (p : Poly) :
    PolyEq (polyMul polyZero p) polyZero := by
  exact PolyEq_refl polyZero

theorem polyMul_cons_right (a : IntegerUp) (p q : Poly) :
    PolyEq (polyMul q (a :: p))
      (polyAdd (polyScale a q) (polyShift (polyMul q p))) := by
  induction q with
  | nil =>
      exact PolyEq_refl polyZero
  | cons b q ih =>
      intro n
      cases n with
      | zero =>
          have leftRaw :
              coeffEq
                (polyCoeff
                  (polyAdd (polyScale b (a :: p))
                    (polyShift (polyMul q (a :: p)))) 0)
                (coeffAdd (coeffMul b a) coeffZero) :=
            intLaws.eq_trans
              (polyCoeff_add (polyScale b (a :: p))
                (polyShift (polyMul q (a :: p))) 0)
              (intLaws.add_respects
                (polyCoeff_scale b (a :: p) 0)
                (polyCoeff_shift_zero (polyMul q (a :: p))))
          have leftHead :
              coeffEq
                (polyCoeff
                  (polyAdd (polyScale b (a :: p))
                    (polyShift (polyMul q (a :: p)))) 0)
                (coeffMul a b) :=
            intLaws.eq_trans leftRaw
              (intLaws.eq_trans (intLaws.add_zero (coeffMul b a))
                (intLaws.mul_comm b a))
          have rightRaw :
              coeffEq
                (polyCoeff
                  (polyAdd (polyScale a (b :: q))
                    (polyShift (polyMul (b :: q) p))) 0)
                (coeffAdd (coeffMul a b) coeffZero) :=
            intLaws.eq_trans
              (polyCoeff_add (polyScale a (b :: q))
                (polyShift (polyMul (b :: q) p)) 0)
              (intLaws.add_respects
                (polyCoeff_scale a (b :: q) 0)
                (polyCoeff_shift_zero (polyMul (b :: q) p)))
          have rightHead :
              coeffEq
                (polyCoeff
                  (polyAdd (polyScale a (b :: q))
                    (polyShift (polyMul (b :: q) p))) 0)
                (coeffMul a b) :=
            intLaws.eq_trans rightRaw (intLaws.add_zero (coeffMul a b))
          exact intLaws.eq_trans leftHead (intLaws.eq_symm rightHead)
      | succ n =>
          have leftRaw :
              coeffEq
                (polyCoeff
                  (polyAdd (polyScale b (a :: p))
                    (polyShift (polyMul q (a :: p)))) (Nat.succ n))
                (coeffAdd (coeffMul b (polyCoeff p n))
                  (polyCoeff (polyMul q (a :: p)) n)) :=
            intLaws.eq_trans
              (polyCoeff_add (polyScale b (a :: p))
                (polyShift (polyMul q (a :: p))) (Nat.succ n))
              (intLaws.add_respects
                (polyCoeff_scale b (a :: p) (Nat.succ n))
                (polyCoeff_shift_succ (polyMul q (a :: p)) n))
          have tailLeft :
              coeffEq (polyCoeff (polyMul q (a :: p)) n)
                (coeffAdd (coeffMul a (polyCoeff q n))
                  (polyCoeff (polyShift (polyMul q p)) n)) :=
            intLaws.eq_trans (ih n)
              (intLaws.eq_trans
                (polyCoeff_add (polyScale a q)
                  (polyShift (polyMul q p)) n)
                (intLaws.add_respects
                  (polyCoeff_scale a q n)
                  (intLaws.eq_refl
                    (polyCoeff (polyShift (polyMul q p)) n))))
          have leftMiddle :
              coeffEq
                (polyCoeff
                (polyAdd (polyScale b (a :: p))
                  (polyShift (polyMul q (a :: p)))) (Nat.succ n))
                (coeffAdd (coeffMul b (polyCoeff p n))
                  (coeffAdd (coeffMul a (polyCoeff q n))
                    (polyCoeff (polyShift (polyMul q p)) n))) :=
            intLaws.eq_trans leftRaw
              (intLaws.add_respects
                (intLaws.eq_refl (coeffMul b (polyCoeff p n))) tailLeft)
          have leftTarget :
              coeffEq
                (polyCoeff
                (polyAdd (polyScale b (a :: p))
                  (polyShift (polyMul q (a :: p)))) (Nat.succ n))
                (coeffAdd (coeffMul a (polyCoeff q n))
                  (coeffAdd (coeffMul b (polyCoeff p n))
                    (polyCoeff (polyShift (polyMul q p)) n))) :=
            intLaws.eq_trans leftMiddle
              (coeffAdd_right_swap
                (coeffMul b (polyCoeff p n))
                (coeffMul a (polyCoeff q n))
                (polyCoeff (polyShift (polyMul q p)) n))
          have rightRaw :
              coeffEq
                (polyCoeff
                  (polyAdd (polyScale a (b :: q))
                    (polyShift (polyMul (b :: q) p))) (Nat.succ n))
                (coeffAdd (coeffMul a (polyCoeff q n))
                  (polyCoeff (polyMul (b :: q) p) n)) :=
            intLaws.eq_trans
              (polyCoeff_add (polyScale a (b :: q))
                (polyShift (polyMul (b :: q) p)) (Nat.succ n))
              (intLaws.add_respects
                (polyCoeff_scale a (b :: q) (Nat.succ n))
                (polyCoeff_shift_succ (polyMul (b :: q) p) n))
          have tailRight :
              coeffEq (polyCoeff (polyMul (b :: q) p) n)
                (coeffAdd (coeffMul b (polyCoeff p n))
                  (polyCoeff (polyShift (polyMul q p)) n)) :=
            intLaws.eq_trans
              (polyCoeff_add (polyScale b p)
                (polyShift (polyMul q p)) n)
              (intLaws.add_respects
                (polyCoeff_scale b p n)
                (intLaws.eq_refl
                  (polyCoeff (polyShift (polyMul q p)) n)))
          have rightTarget :
              coeffEq
                (polyCoeff
                (polyAdd (polyScale a (b :: q))
                  (polyShift (polyMul (b :: q) p))) (Nat.succ n))
                (coeffAdd (coeffMul a (polyCoeff q n))
                  (coeffAdd (coeffMul b (polyCoeff p n))
                    (polyCoeff (polyShift (polyMul q p)) n))) :=
            intLaws.eq_trans rightRaw
              (intLaws.add_respects
                (intLaws.eq_refl (coeffMul a (polyCoeff q n))) tailRight)
          exact intLaws.eq_trans leftTarget (intLaws.eq_symm rightTarget)

theorem polyMul_comm (p q : Poly) :
    PolyEq (polyMul p q) (polyMul q p) := by
  induction p with
  | nil =>
      exact PolyEq_symm (polyMul_zero q)
  | cons a p ih =>
      exact PolyEq_trans
        (polyAdd_respects (PolyEq_refl (polyScale a q))
          (polyShift_respects ih))
        (PolyEq_symm (polyMul_cons_right a p q))

theorem polyMul_respects_right (p : Poly) {q q' : Poly} :
    PolyEq q q' -> PolyEq (polyMul p q) (polyMul p q') := by
  intro qq'
  induction p with
  | nil =>
      exact PolyEq_refl polyZero
  | cons a p ih =>
      exact polyAdd_respects (polyScale_respects (intLaws.eq_refl a) qq')
        (polyShift_respects ih)

theorem polyMul_respects_left {p p' : Poly} (q : Poly) :
    PolyEq p p' -> PolyEq (polyMul p q) (polyMul p' q) := by
  intro pp'
  exact PolyEq_trans (polyMul_comm p q)
    (PolyEq_trans (polyMul_respects_right q pp') (polyMul_comm q p'))

theorem polyMul_respects {p p' q q' : Poly} :
    PolyEq p p' -> PolyEq q q' -> PolyEq (polyMul p q) (polyMul p' q') := by
  intro pp' qq'
  exact PolyEq_trans (polyMul_respects_left q pp')
    (polyMul_respects_right p' qq')

theorem polyMul_add_distrib (p q r : Poly) :
    PolyEq (polyMul p (polyAdd q r))
      (polyAdd (polyMul p q) (polyMul p r)) := by
  induction p with
  | nil =>
      exact PolyEq_refl polyZero
  | cons a p ih =>
      exact PolyEq_trans
        (polyAdd_respects (polyScale_add a q r) (polyShift_respects ih))
        (PolyEq_trans
          (polyAdd_respects (PolyEq_refl (polyAdd (polyScale a q) (polyScale a r)))
            (polyShift_add (polyMul p q) (polyMul p r)))
          (polyAdd_four_swap (polyScale a q) (polyScale a r)
            (polyShift (polyMul p q)) (polyShift (polyMul p r))))

theorem polyMul_add_distrib_right (p q r : Poly) :
    PolyEq (polyMul (polyAdd p q) r)
      (polyAdd (polyMul p r) (polyMul q r)) := by
  exact PolyEq_trans (polyMul_comm (polyAdd p q) r)
    (PolyEq_trans (polyMul_add_distrib r p q)
      (polyAdd_respects (polyMul_comm r p) (polyMul_comm r q)))

theorem polyMul_one_left (p : Poly) :
    PolyEq (polyMul polyOne p) p := by
  exact PolyEq_trans
    (polyAdd_right_zero_of_eqv
      (p := polyScale coeffOne p)
      (q := polyShift (polyMul polyZero p))
      (polyShift_zero_of_eqv (polyMul_zero_left p)))
    (polyScale_one_left p)

theorem polyMul_one (p : Poly) :
    PolyEq (polyMul p polyOne) p := by
  exact PolyEq_trans (polyMul_comm p polyOne) (polyMul_one_left p)

theorem polyScale_mul_left (a : IntegerUp) (p q : Poly) :
    PolyEq (polyMul (polyScale a p) q) (polyScale a (polyMul p q)) := by
  induction p with
  | nil =>
      exact PolyEq_refl polyZero
  | cons b p ih =>
      exact PolyEq_trans
        (polyAdd_respects (polyScale_scale a b q) (polyShift_respects ih))
        (PolyEq_trans
          (polyAdd_respects
            (PolyEq_refl (polyScale a (polyScale b q)))
            (PolyEq_symm (polyScale_shift a (polyMul p q))))
          (PolyEq_symm
            (polyScale_add a (polyScale b q) (polyShift (polyMul p q)))))

theorem polyShift_mul_left (p q : Poly) :
    PolyEq (polyMul (polyShift p) q) (polyShift (polyMul p q)) := by
  cases p with
  | nil =>
      exact PolyEq_refl polyZero
  | cons a p =>
      exact polyAdd_left_zero_of_eqv
        (p := polyScale coeffZero q)
        (q := polyShift (polyMul (a :: p) q))
        (polyScale_zero_left q)

theorem polyMul_assoc (p q r : Poly) :
    PolyEq (polyMul (polyMul p q) r) (polyMul p (polyMul q r)) := by
  induction p with
  | nil =>
      exact PolyEq_refl polyZero
  | cons a p ih =>
      exact PolyEq_trans
        (polyMul_add_distrib_right (polyScale a q) (polyShift (polyMul p q)) r)
        (PolyEq_trans
          (polyAdd_respects (polyScale_mul_left a q r)
            (polyShift_mul_left (polyMul p q) r))
          (polyAdd_respects
            (PolyEq_refl (polyScale a (polyMul q r)))
            (polyShift_respects ih)))

structure PolynomialCommRingLaws where
  eq_refl : ∀ p : Poly, PolyEq p p
  eq_symm : ∀ {p q : Poly}, PolyEq p q -> PolyEq q p
  eq_trans : ∀ {p q r : Poly}, PolyEq p q -> PolyEq q r -> PolyEq p r
  add_respects :
    ∀ {p p' q q' : Poly}, PolyEq p p' -> PolyEq q q' ->
      PolyEq (polyAdd p q) (polyAdd p' q')
  mul_respects :
    ∀ {p p' q q' : Poly}, PolyEq p p' -> PolyEq q q' ->
      PolyEq (polyMul p q) (polyMul p' q')
  neg_respects : ∀ {p q : Poly}, PolyEq p q -> PolyEq (polyNeg p) (polyNeg q)
  add_comm : ∀ p q : Poly, PolyEq (polyAdd p q) (polyAdd q p)
  add_assoc :
    ∀ p q r : Poly,
      PolyEq (polyAdd (polyAdd p q) r) (polyAdd p (polyAdd q r))
  add_zero : ∀ p : Poly, PolyEq (polyAdd p polyZero) p
  zero_add : ∀ p : Poly, PolyEq (polyAdd polyZero p) p
  add_neg : ∀ p : Poly, PolyEq (polyAdd p (polyNeg p)) polyZero
  neg_add : ∀ p : Poly, PolyEq (polyAdd (polyNeg p) p) polyZero
  mul_comm : ∀ p q : Poly, PolyEq (polyMul p q) (polyMul q p)
  mul_assoc :
    ∀ p q r : Poly,
      PolyEq (polyMul (polyMul p q) r) (polyMul p (polyMul q r))
  mul_one : ∀ p : Poly, PolyEq (polyMul p polyOne) p
  one_mul : ∀ p : Poly, PolyEq (polyMul polyOne p) p
  mul_zero : ∀ p : Poly, PolyEq (polyMul p polyZero) polyZero
  zero_mul : ∀ p : Poly, PolyEq (polyMul polyZero p) polyZero
  left_distrib :
    ∀ p q r : Poly,
      PolyEq (polyMul p (polyAdd q r))
        (polyAdd (polyMul p q) (polyMul p r))
  right_distrib :
    ∀ p q r : Poly,
      PolyEq (polyMul (polyAdd p q) r)
        (polyAdd (polyMul p r) (polyMul q r))

def polynomial_comm_ring_laws : PolynomialCommRingLaws where
  eq_refl := PolyEq_refl
  eq_symm := by
    intro p q
    exact PolyEq_symm
  eq_trans := by
    intro p q r
    exact PolyEq_trans
  add_respects := by
    intro p p' q q'
    exact polyAdd_respects
  mul_respects := by
    intro p p' q q'
    exact polyMul_respects
  neg_respects := by
    intro p q
    exact polyNeg_respects
  add_comm := polyAdd_comm
  add_assoc := polyAdd_assoc
  add_zero := polyAdd_zero
  zero_add := polyAdd_zero_left
  add_neg := polyAdd_neg
  neg_add := polyAdd_neg_left
  mul_comm := polyMul_comm
  mul_assoc := polyMul_assoc
  mul_one := polyMul_one
  one_mul := polyMul_one_left
  mul_zero := polyMul_zero
  zero_mul := polyMul_zero_left
  left_distrib := polyMul_add_distrib
  right_distrib := polyMul_add_distrib_right

end BEDC.Derived.PolynomialUp
