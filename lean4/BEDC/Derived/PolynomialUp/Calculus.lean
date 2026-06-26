import BEDC.Derived.PolynomialUp.IntegerRing

namespace BEDC.Derived.PolynomialUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength bwordLength_append)

private abbrev zZero : IntegerUp :=
  BEDC.Derived.RationalUp.intZero

private abbrev zOne : IntegerUp :=
  BEDC.Derived.RationalUp.intOne

private abbrev zAdd : IntegerUp -> IntegerUp -> IntegerUp :=
  BEDC.Derived.RationalUp.IntAdd

private abbrev zMul : IntegerUp -> IntegerUp -> IntegerUp :=
  BEDC.Derived.RationalUp.IntMul

private abbrev zEq : IntegerUp -> IntegerUp -> Prop :=
  BEDC.Derived.RationalUp.IntEq

private abbrev zLaws : BEDC.Derived.IntUp.IntegerUpCommRingLaws :=
  BEDC.Derived.IntUp.IntegerUp_comm_ring_laws

private theorem zAdd_right_swap (a b c : IntegerUp) :
    zEq (zAdd a (zAdd b c)) (zAdd b (zAdd a c)) :=
  zLaws.eq_trans (zLaws.eq_symm (zLaws.add_assoc a b c))
    (zLaws.eq_trans
      (zLaws.add_respects (zLaws.add_comm a b) (zLaws.eq_refl c))
      (zLaws.add_assoc b a c))

private theorem zAdd_four_swap (a b c d : IntegerUp) :
    zEq (zAdd (zAdd a b) (zAdd c d))
      (zAdd (zAdd a c) (zAdd b d)) :=
  zLaws.eq_trans (zLaws.add_assoc a b (zAdd c d))
    (zLaws.eq_trans
      (zLaws.add_respects (zLaws.eq_refl a) (zAdd_right_swap b c d))
      (zLaws.eq_symm (zLaws.add_assoc a c (zAdd b d))))

private theorem zMul_left_swap (a b c : IntegerUp) :
    zEq (zMul a (zMul b c)) (zMul b (zMul a c)) :=
  zLaws.eq_trans (zLaws.eq_symm (zLaws.mul_assoc a b c))
    (zLaws.eq_trans
      (zLaws.mul_respects (zLaws.mul_comm a b) (zLaws.eq_refl c))
      (zLaws.mul_assoc b a c))

private theorem zAdd_leibniz_shuffle (a b c d : IntegerUp) :
    zEq (zAdd a (zAdd b (zAdd c d)))
      (zAdd (zAdd b c) (zAdd a d)) :=
  zLaws.eq_trans (zLaws.eq_symm (zLaws.add_assoc a b (zAdd c d)))
    (zLaws.eq_trans
      (zLaws.add_respects (zLaws.add_comm a b) (zLaws.eq_refl (zAdd c d)))
      (zAdd_four_swap b a c d))

private theorem coeffOfNat_succ (n : Nat) :
    zEq (coeffOfNat (Nat.succ n)) (zAdd zOne (coeffOfNat n)) := by
  unfold zEq
  have addPair :
      BEDC.Derived.IntUp.IntPairClassifier
        (BEDC.Derived.RationalUp.intToPair (zAdd zOne (coeffOfNat n)))
        (BEDC.Derived.IntUp.pairAdd
          (BEDC.Derived.RationalUp.intToPair zOne)
          (BEDC.Derived.RationalUp.intToPair (coeffOfNat n))) :=
    BEDC.Derived.RationalUp.intAdd_pair_classifier zOne (coeffOfNat n)
  have succPair :
      BEDC.Derived.IntUp.IntPairClassifier
        (BEDC.Derived.RationalUp.intToPair (coeffOfNat (Nat.succ n)))
        (BEDC.Derived.IntUp.pairAdd
          (BEDC.Derived.RationalUp.intToPair zOne)
          (BEDC.Derived.RationalUp.intToPair (coeffOfNat n))) := by
    apply BEDC.Derived.RationalUp.IntPairClassifier_of_length_eq
      (BEDC.Derived.RationalUp.intToPair_carrier (coeffOfNat (Nat.succ n)))
      (BEDC.Derived.IntUp.pairAdd_carrier
        (BEDC.Derived.RationalUp.intToPair_carrier zOne)
        (BEDC.Derived.RationalUp.intToPair_carrier (coeffOfNat n)))
    unfold coeffOfNat zOne BEDC.Derived.RationalUp.intOne
      BEDC.Derived.RationalUp.intOfNat BEDC.Derived.RationalUp.intToPair
      BEDC.Derived.IntUp.pairAdd
    change
      bwordLength (BEDC.Derived.IntUp.natToUnary (Nat.succ n)) +
          bwordLength BHist.Empty =
        bwordLength
            (BEDC.FKernel.Cont.append
              (BHist.e1 BHist.Empty)
              (BEDC.Derived.IntUp.natToUnary n)) +
          bwordLength (BEDC.FKernel.Cont.append BHist.Empty BHist.Empty)
    rw [BEDC.Derived.IntUp.natToUnary_length]
    rw [bwordLength_append]
    rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.left
      BHist.Empty unary_empty]
    rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
    rw [BEDC.Derived.IntUp.natToUnary_length]
    rw [BEDC.FKernel.Cont.append_empty_right]
    rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
    rw [Nat.add_zero]
    change n + 1 = 1 + n
    exact Nat.add_comm n 1
  exact BEDC.Derived.IntUp.IntPairClassifier_equivalence_fields.right.right.right.right.left
    succPair
    (BEDC.Derived.IntUp.IntPairClassifier_equivalence_fields.right.right.right.left addPair)

private theorem coeffOfNat_succ_mul (n : Nat) (a : IntegerUp) :
    zEq (zMul (coeffOfNat (Nat.succ n)) a)
      (zAdd a (zMul (coeffOfNat n) a)) :=
  zLaws.eq_trans
    (zLaws.mul_respects (coeffOfNat_succ n) (zLaws.eq_refl a))
    (zLaws.eq_trans
      (zLaws.right_distrib zOne (coeffOfNat n) a)
      (zLaws.add_respects (zLaws.one_mul a)
        (zLaws.eq_refl (zMul (coeffOfNat n) a))))

theorem polyEval_add (x : IntegerUp) (p q : Poly) :
    BEDC.Derived.RationalUp.IntEq (polyEval x (polyAdd p q))
      (BEDC.Derived.RationalUp.IntAdd (polyEval x p) (polyEval x q)) := by
  induction p generalizing q with
  | nil =>
      change zEq (polyEval x q) (zAdd zZero (polyEval x q))
      exact zLaws.eq_symm (zLaws.zero_add (polyEval x q))
  | cons a p ih =>
      cases q with
      | nil =>
          change zEq (polyEval x (a :: p)) (zAdd (polyEval x (a :: p)) zZero)
          exact zLaws.eq_symm (zLaws.add_zero (polyEval x (a :: p)))
      | cons b q =>
          change
            zEq
              (zAdd (zAdd a b) (zMul x (polyEval x (polyAdd p q))))
              (zAdd (zAdd a (zMul x (polyEval x p)))
                (zAdd b (zMul x (polyEval x q))))
          have tailMul :
              zEq (zMul x (polyEval x (polyAdd p q)))
                (zMul x (zAdd (polyEval x p) (polyEval x q))) :=
            zLaws.mul_respects (zLaws.eq_refl x) (ih q)
          have tailDistrib :
              zEq (zMul x (polyEval x (polyAdd p q)))
                (zAdd (zMul x (polyEval x p)) (zMul x (polyEval x q))) :=
            zLaws.eq_trans tailMul
              (zLaws.left_distrib x (polyEval x p) (polyEval x q))
          exact zLaws.eq_trans
            (zLaws.add_respects (zLaws.eq_refl (zAdd a b)) tailDistrib)
            (zAdd_four_swap a b (zMul x (polyEval x p)) (zMul x (polyEval x q)))

theorem polyEval_scale (x a : IntegerUp) (p : Poly) :
    BEDC.Derived.RationalUp.IntEq (polyEval x (polyScale a p))
      (BEDC.Derived.RationalUp.IntMul a (polyEval x p)) := by
  induction p with
  | nil =>
      change zEq zZero (zMul a zZero)
      exact zLaws.eq_symm (zLaws.mul_zero a)
  | cons b p ih =>
      change
        zEq (zAdd (zMul a b) (zMul x (polyEval x (polyScale a p))))
          (zMul a (zAdd b (zMul x (polyEval x p))))
      have tail :
          zEq (zMul x (polyEval x (polyScale a p)))
            (zMul x (zMul a (polyEval x p))) :=
        zLaws.mul_respects (zLaws.eq_refl x) ih
      have swapped :
          zEq (zMul x (zMul a (polyEval x p)))
            (zMul a (zMul x (polyEval x p))) :=
        zLaws.eq_symm (zMul_left_swap a x (polyEval x p))
      exact zLaws.eq_trans
        (zLaws.add_respects (zLaws.eq_refl (zMul a b))
          (zLaws.eq_trans tail swapped))
        (zLaws.eq_symm (zLaws.left_distrib a b (zMul x (polyEval x p))))

theorem polyEval_shift (x : IntegerUp) (p : Poly) :
    BEDC.Derived.RationalUp.IntEq (polyEval x (polyShift p))
      (BEDC.Derived.RationalUp.IntMul x (polyEval x p)) := by
  cases p with
  | nil =>
      change zEq zZero (zMul x zZero)
      exact zLaws.eq_symm (zLaws.mul_zero x)
  | cons a p =>
      change
        zEq (zAdd zZero (zMul x (polyEval x (a :: p))))
          (zMul x (polyEval x (a :: p)))
      exact zLaws.zero_add (zMul x (polyEval x (a :: p)))

theorem polyEval_mul (x : IntegerUp) (p q : Poly) :
    BEDC.Derived.RationalUp.IntEq (polyEval x (polyMul p q))
      (BEDC.Derived.RationalUp.IntMul (polyEval x p) (polyEval x q)) := by
  induction p with
  | nil =>
      change zEq zZero (zMul zZero (polyEval x q))
      exact zLaws.eq_symm (zLaws.zero_mul (polyEval x q))
  | cons a p ih =>
      change
        zEq
          (polyEval x
            (polyAdd (polyScale a q) (polyShift (polyMul p q))))
          (zMul (zAdd a (zMul x (polyEval x p))) (polyEval x q))
      have addEval := polyEval_add x (polyScale a q) (polyShift (polyMul p q))
      have scaleEval := polyEval_scale x a q
      have shiftEval := polyEval_shift x (polyMul p q)
      have evalParts :
          zEq
            (zAdd (polyEval x (polyScale a q))
              (polyEval x (polyShift (polyMul p q))))
            (zAdd (zMul a (polyEval x q))
              (zMul x (polyEval x (polyMul p q)))) :=
        zLaws.add_respects scaleEval shiftEval
      have tailEval :
          zEq (zMul x (polyEval x (polyMul p q)))
            (zMul x (zMul (polyEval x p) (polyEval x q))) :=
        zLaws.mul_respects (zLaws.eq_refl x) ih
      have assocTail :
          zEq (zMul x (zMul (polyEval x p) (polyEval x q)))
            (zMul (zMul x (polyEval x p)) (polyEval x q)) :=
        zLaws.eq_symm (zLaws.mul_assoc x (polyEval x p) (polyEval x q))
      have rightDistrib :
          zEq
            (zAdd (zMul a (polyEval x q))
              (zMul (zMul x (polyEval x p)) (polyEval x q)))
            (zMul (zAdd a (zMul x (polyEval x p))) (polyEval x q)) :=
        zLaws.eq_symm
          (zLaws.right_distrib a (zMul x (polyEval x p)) (polyEval x q))
      exact zLaws.eq_trans addEval
        (zLaws.eq_trans evalParts
          (zLaws.eq_trans
            (zLaws.add_respects (zLaws.eq_refl (zMul a (polyEval x q)))
              (zLaws.eq_trans tailEval assocTail))
            rightDistrib))

theorem polyDerivFrom_add (n : Nat) (p q : Poly) :
    PolyEq (polyDerivFrom n (polyAdd p q))
      (polyAdd (polyDerivFrom n p) (polyDerivFrom n q)) := by
  intro k
  induction p generalizing q n k with
  | nil =>
      change zEq (polyCoeff (polyDerivFrom n q) k)
        (polyCoeff (polyDerivFrom n q) k)
      exact zLaws.eq_refl (polyCoeff (polyDerivFrom n q) k)
  | cons a p ih =>
      cases q with
      | nil =>
          change zEq (polyCoeff (polyDerivFrom n (a :: p)) k)
            (polyCoeff (polyDerivFrom n (a :: p)) k)
          exact zLaws.eq_refl (polyCoeff (polyDerivFrom n (a :: p)) k)
      | cons b q =>
          cases k with
          | zero =>
              change
                zEq (zMul (coeffOfNat n) (zAdd a b))
                  (zAdd (zMul (coeffOfNat n) a) (zMul (coeffOfNat n) b))
              exact zLaws.left_distrib (coeffOfNat n) a b
          | succ k =>
              change
                zEq (polyCoeff (polyDerivFrom (Nat.succ n) (polyAdd p q)) k)
                  (polyCoeff
                    (polyAdd (polyDerivFrom (Nat.succ n) p)
                      (polyDerivFrom (Nat.succ n) q)) k)
              exact ih (Nat.succ n) q k

theorem polyDeriv_add (p q : Poly) :
    PolyEq (polyDeriv (polyAdd p q))
      (polyAdd (polyDeriv p) (polyDeriv q)) := by
  cases p with
  | nil =>
      exact PolyEq_refl (polyDeriv q)
  | cons a p =>
      cases q with
      | nil =>
          exact PolyEq_symm (polyAdd_zero (polyDeriv (a :: p)))
      | cons b q =>
          exact polyDerivFrom_add 1 p q

theorem polyDerivFrom_scale (n : Nat) (a : IntegerUp) (p : Poly) :
    PolyEq (polyDerivFrom n (polyScale a p))
      (polyScale a (polyDerivFrom n p)) := by
  induction p generalizing n with
  | nil =>
      exact PolyEq_refl polyZero
  | cons b p ih =>
      intro k
      cases k with
      | zero =>
          change zEq (zMul (coeffOfNat n) (zMul a b))
            (zMul a (zMul (coeffOfNat n) b))
          exact zMul_left_swap (coeffOfNat n) a b
      | succ k =>
          exact ih (Nat.succ n) k

theorem polyDeriv_scale (a : IntegerUp) (p : Poly) :
    PolyEq (polyDeriv (polyScale a p)) (polyScale a (polyDeriv p)) := by
  cases p with
  | nil =>
      exact PolyEq_refl polyZero
  | cons b p =>
      exact polyDerivFrom_scale 1 a p

theorem polyDerivFrom_succ_add (n : Nat) (p : Poly) :
    PolyEq (polyDerivFrom (Nat.succ n) p)
      (polyAdd p (polyDerivFrom n p)) := by
  induction p generalizing n with
  | nil =>
      exact PolyEq_refl polyZero
  | cons a p ih =>
      intro k
      cases k with
      | zero =>
          change zEq (zMul (coeffOfNat (Nat.succ n)) a)
            (zAdd a (zMul (coeffOfNat n) a))
          exact coeffOfNat_succ_mul n a
      | succ k =>
          exact ih (Nat.succ n) k

theorem polyDeriv_shift (p : Poly) :
    PolyEq (polyDeriv (polyShift p))
      (polyAdd p (polyShift (polyDeriv p))) := by
  cases p with
  | nil =>
      exact PolyEq_refl polyZero
  | cons a p =>
      intro k
      cases k with
      | zero =>
          change
            zEq (zMul (coeffOfNat 1) a)
              (polyCoeff (polyAdd (a :: p)
                (polyShift (polyDeriv (a :: p)))) 0)
          exact zLaws.eq_trans
            (zLaws.one_mul a)
              (zLaws.eq_symm
                (zLaws.eq_trans
                  (polyCoeff_add (a :: p) (polyShift (polyDeriv (a :: p))) 0)
                  (zLaws.eq_trans
                    (zLaws.add_respects (zLaws.eq_refl a)
                      (polyCoeff_shift_zero (polyDeriv (a :: p))))
                    (zLaws.add_zero a))))
      | succ k =>
          change
            zEq (polyCoeff (polyDerivFrom 2 p) k)
              (polyCoeff (polyAdd (a :: p)
                (polyShift (polyDeriv (a :: p)))) (Nat.succ k))
          have rightCoeff :
              zEq
                (polyCoeff (polyAdd (a :: p)
                  (polyShift (polyDeriv (a :: p)))) (Nat.succ k))
                (polyCoeff (polyAdd p (polyDerivFrom 1 p)) k) :=
            zLaws.eq_trans
              (polyCoeff_add (a :: p) (polyShift (polyDeriv (a :: p))) (Nat.succ k))
              (zLaws.eq_trans
                (zLaws.add_respects
                  (zLaws.eq_refl (polyCoeff p k))
                  (polyCoeff_shift_succ (polyDeriv (a :: p)) k))
                (zLaws.eq_symm (polyCoeff_add p (polyDerivFrom 1 p) k)))
          exact zLaws.eq_trans
            ((polyDerivFrom_succ_add 1 p) k)
            (zLaws.eq_symm rightCoeff)

private theorem polyAdd_leibniz_shuffle (a b c d : Poly) :
    PolyEq (polyAdd a (polyAdd b (polyAdd c d)))
      (polyAdd (polyAdd b c) (polyAdd a d)) := by
  intro n
  exact zLaws.eq_trans (polyCoeff_add a (polyAdd b (polyAdd c d)) n)
    (zLaws.eq_trans
      (zLaws.add_respects (zLaws.eq_refl (polyCoeff a n))
        (polyCoeff_add b (polyAdd c d) n))
      (zLaws.eq_trans
        (zLaws.add_respects (zLaws.eq_refl (polyCoeff a n))
          (zLaws.add_respects (zLaws.eq_refl (polyCoeff b n))
            (polyCoeff_add c d n)))
        (zLaws.eq_trans
          (zAdd_leibniz_shuffle (polyCoeff a n) (polyCoeff b n)
            (polyCoeff c n) (polyCoeff d n))
          (zLaws.eq_symm
            (zLaws.eq_trans (polyCoeff_add (polyAdd b c) (polyAdd a d) n)
              (zLaws.add_respects
                (polyCoeff_add b c n) (polyCoeff_add a d n)))))))

theorem polyDeriv_mul (p q : Poly) :
    PolyEq (polyDeriv (polyMul p q))
      (polyAdd (polyMul (polyDeriv p) q) (polyMul p (polyDeriv q))) := by
  induction p with
  | nil =>
      exact PolyEq_refl polyZero
  | cons a p ih =>
      let dq := polyDeriv q
      let dp := polyDeriv p
      let pq := polyMul p q
      have leftAdd :
          PolyEq (polyDeriv (polyMul (a :: p) q))
            (polyAdd (polyDeriv (polyScale a q))
              (polyDeriv (polyShift pq))) :=
        polyDeriv_add (polyScale a q) (polyShift pq)
      have scaleD :
          PolyEq (polyDeriv (polyScale a q)) (polyScale a dq) :=
        polyDeriv_scale a q
      have shiftD :
          PolyEq (polyDeriv (polyShift pq))
            (polyAdd pq (polyShift (polyDeriv pq))) :=
        polyDeriv_shift pq
      have leftNormal :
          PolyEq (polyDeriv (polyMul (a :: p) q))
            (polyAdd (polyScale a dq)
              (polyAdd pq
                (polyAdd (polyShift (polyMul dp q))
                  (polyShift (polyMul p dq))))) :=
        PolyEq_trans leftAdd
          (PolyEq_trans
            (polyAdd_respects scaleD shiftD)
            (polyAdd_respects (PolyEq_refl (polyScale a dq))
              (polyAdd_respects (PolyEq_refl pq)
                (PolyEq_trans
                  (polyShift_respects ih)
                  (polyShift_add (polyMul dp q) (polyMul p dq))))))
      have derivHead :
          PolyEq (polyDeriv (a :: p)) (polyAdd p (polyShift dp)) :=
        by
          cases p with
          | nil =>
              exact PolyEq_refl polyZero
          | cons b p =>
              exact polyDeriv_shift (b :: p)
      have firstProduct :
          PolyEq (polyMul (polyDeriv (a :: p)) q)
            (polyAdd pq (polyShift (polyMul dp q))) :=
        PolyEq_trans
          (polyMul_respects_left q derivHead)
          (PolyEq_trans
            (polyMul_add_distrib_right p (polyShift dp) q)
            (polyAdd_respects (PolyEq_refl pq)
              (polyShift_mul_left dp q)))
      have secondProduct :
          PolyEq (polyMul (a :: p) dq)
            (polyAdd (polyScale a dq) (polyShift (polyMul p dq))) :=
        PolyEq_refl (polyMul (a :: p) dq)
      have targetNormal :
          PolyEq
            (polyAdd (polyMul (polyDeriv (a :: p)) q)
              (polyMul (a :: p) dq))
            (polyAdd (polyAdd pq (polyShift (polyMul dp q)))
              (polyAdd (polyScale a dq) (polyShift (polyMul p dq)))) :=
        polyAdd_respects firstProduct secondProduct
      exact PolyEq_trans leftNormal
        (PolyEq_trans
          (polyAdd_leibniz_shuffle (polyScale a dq) pq
            (polyShift (polyMul dp q)) (polyShift (polyMul p dq)))
          (PolyEq_symm targetNormal))

end BEDC.Derived.PolynomialUp
