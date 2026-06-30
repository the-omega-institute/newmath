import BEDC.Algebra.FiniteFold
import BEDC.Derived.DirichletRingUp
import BEDC.Derived.IntUp.CommRing
import BEDC.Real.RatNumKernel

namespace BEDC.Derived.AbelSummationUp

open BEDC.Algebra.Rel
open BEDC.Algebra.FiniteFold

variable {A : Type u} {r : A -> A -> Prop}

abbrev AbelRow (A : Type u) := A × A

def rowProduct (R : RelCommRing A r) (row : AbelRow A) : A :=
  R.mul row.1 row.2

def weightedTermSum (R : RelCommRing A r) (rows : List (AbelRow A)) : A :=
  listSum R (rows.map (rowProduct R))

def prefixAfter (R : RelCommRing A r) : A -> List (AbelRow A) -> A
  | prior, [] => prior
  | prior, row :: rows => prefixAfter R (R.add prior row.1) rows

def firstWeight (fallback : A) : List (AbelRow A) -> A
  | [] => fallback
  | row :: _rows => row.2

def lastWeight (fallback : A) : List (AbelRow A) -> A
  | [] => fallback
  | row :: [] => row.2
  | _row :: next :: rows => lastWeight fallback (next :: rows)

def terminalProduct (R : RelCommRing A r) (prior : A)
    (rows : List (AbelRow A)) : A :=
  R.mul (prefixAfter R prior rows) (lastWeight R.zero rows)

def forwardDifferenceTermsFrom (R : RelCommRing A r) :
    A -> List (AbelRow A) -> List A
  | _prior, [] => []
  | _prior, _row :: [] => []
  | prior, row :: next :: rows =>
      let current := R.add prior row.1
      R.mul current (R.sub next.2 row.2) ::
        forwardDifferenceTermsFrom R current (next :: rows)

def forwardDifferenceSumFrom (R : RelCommRing A r) (prior : A)
    (rows : List (AbelRow A)) : A :=
  listSum R (forwardDifferenceTermsFrom R prior rows)

def abelPartialSummationRight (R : RelCommRing A r)
    (rows : List (AbelRow A)) : A :=
  R.sub (terminalProduct R R.zero rows)
    (forwardDifferenceSumFrom R R.zero rows)

abbrev AbelPoint (A : Type u) := A × A

def pointProduct (R : RelCommRing A r) (point : AbelPoint A) : A :=
  R.mul point.1 point.2

def pointWeightDifferenceTerm (R : RelCommRing A r)
    (point next : AbelPoint A) : A :=
  R.mul point.1 (R.sub next.2 point.2)

def pointNextWeightDifferenceTerm (R : RelCommRing A r)
    (point next : AbelPoint A) : A :=
  R.mul next.2 (R.sub next.1 point.1)

def pointProductJump (R : RelCommRing A r)
    (point next : AbelPoint A) : A :=
  R.sub (pointProduct R next) (pointProduct R point)

def finalPoint : AbelPoint A -> List (AbelPoint A) -> AbelPoint A
  | point, [] => point
  | _point, next :: rest => finalPoint next rest

def pointWeightDifferenceTermsFrom (R : RelCommRing A r) :
    AbelPoint A -> List (AbelPoint A) -> List A
  | _point, [] => []
  | point, next :: rest =>
      pointWeightDifferenceTerm R point next ::
        pointWeightDifferenceTermsFrom R next rest

def pointNextWeightDifferenceTermsFrom (R : RelCommRing A r) :
    AbelPoint A -> List (AbelPoint A) -> List A
  | _point, [] => []
  | point, next :: rest =>
      pointNextWeightDifferenceTerm R point next ::
        pointNextWeightDifferenceTermsFrom R next rest

private theorem add_sub_cancel_left_arg (R : RelCommRing A r) (x y : A) :
    r (R.add x (R.sub y x)) y := by
  exact R.trans (R.add_congr (R.refl x) (R.sub_eq_add_neg y x))
    (R.trans (R.symm (R.add_assoc x y (R.neg x)))
      (R.trans
        (R.add_congr (R.add_comm x y) (R.refl (R.neg x)))
        (R.trans (R.add_assoc y x (R.neg x))
          (R.trans (R.add_congr (R.refl y) (R.add_neg x))
            (R.add_zero y)))))

private theorem eq_sub_of_add_eq (R : RelCommRing A r) {x y z : A} :
    r (R.add x y) z -> r x (R.sub z y) := by
  intro h
  have cancel :
      r (R.add (R.add x y) (R.neg y)) x := by
    exact R.trans (R.add_assoc x y (R.neg y))
      (R.trans (R.add_congr (R.refl x) (R.add_neg y))
        (R.add_zero x))
  exact R.trans (R.symm cancel)
    (R.trans (R.add_congr h (R.refl (R.neg y)))
      (R.symm (R.sub_eq_add_neg z y)))

private theorem prefix_mul_balance (R : RelCommRing A r)
    (prior a b : A) :
    r (R.add (R.mul a b) (R.mul prior b))
      (R.mul (R.add prior a) b) := by
  exact R.trans (R.add_comm (R.mul a b) (R.mul prior b))
    (R.symm (R.right_distrib prior a b))

private theorem mul_sub_right (R : RelCommRing A r)
    (x y z : A) :
    r (R.mul x (R.sub y z))
      (R.sub (R.mul x y) (R.mul x z)) := by
  exact R.trans (R.mul_congr (R.refl x) (R.sub_eq_add_neg y z))
    (R.trans (R.left_distrib x y (R.neg z))
      (R.trans
        (R.add_congr (R.refl (R.mul x y)) (R.mul_neg x z))
        (R.symm (R.sub_eq_add_neg (R.mul x y) (R.mul x z)))))

private theorem head_forward_balance (R : RelCommRing A r)
    (prior a b nextB : A) :
    r
      (R.add (R.mul a b)
        (R.add (R.mul prior b)
          (R.mul (R.add prior a) (R.sub nextB b))))
      (R.mul (R.add prior a) nextB) := by
  have prefixStep :
      r (R.add (R.mul a b) (R.mul prior b))
        (R.mul (R.add prior a) b) :=
    prefix_mul_balance R prior a b
  have delta :
      r (R.mul (R.add prior a) (R.sub nextB b))
        (R.sub (R.mul (R.add prior a) nextB)
          (R.mul (R.add prior a) b)) :=
    mul_sub_right R (R.add prior a) nextB b
  exact R.trans (R.symm
      (R.add_assoc (R.mul a b) (R.mul prior b)
        (R.mul (R.add prior a) (R.sub nextB b))))
    (R.trans (R.add_congr prefixStep delta)
      (add_sub_cancel_left_arg R
        (R.mul (R.add prior a) b)
        (R.mul (R.add prior a) nextB)))

private theorem add_five_rebracket (R : RelCommRing A r)
    (a b c d e : A) :
    r (R.add (R.add a b) (R.add c (R.add d e)))
      (R.add b (R.add (R.add a (R.add c d)) e)) := by
  have stepOne :
      r (R.add (R.add a b) (R.add c (R.add d e)))
        (R.add (R.add b a) (R.add c (R.add d e))) :=
    R.add_congr (R.add_comm a b) (R.refl (R.add c (R.add d e)))
  have stepTwo :
      r (R.add (R.add b a) (R.add c (R.add d e)))
        (R.add b (R.add a (R.add c (R.add d e)))) :=
    R.add_assoc b a (R.add c (R.add d e))
  have inner :
      r (R.add a (R.add c (R.add d e)))
        (R.add (R.add a (R.add c d)) e) := by
    exact R.trans
      (R.add_congr (R.refl a) (R.symm (R.add_assoc c d e)))
      (R.symm (R.add_assoc a (R.add c d) e))
  exact R.trans stepOne
    (R.trans stepTwo
      (R.add_congr (R.refl b) inner))

private theorem sub_self_zero (R : RelCommRing A r) (x : A) :
    r (R.sub x x) R.zero :=
  R.trans (R.sub_eq_add_neg x x) (R.add_neg x)

private theorem sub_add_cancel_right_arg (R : RelCommRing A r)
    (x y : A) :
    r (R.add (R.sub y x) x) y :=
  R.trans (R.add_comm (R.sub y x) x) (add_sub_cancel_left_arg R x y)

private theorem sub_congr (R : RelCommRing A r)
    {x x' y y' : A} :
    r x x' -> r y y' -> r (R.sub x y) (R.sub x' y') := by
  intro hx hy
  exact R.trans (R.sub_eq_add_neg x y)
    (R.trans (R.add_congr hx (R.neg_congr hy))
      (R.symm (R.sub_eq_add_neg x' y')))

private theorem sub_chain (R : RelCommRing A r) (x y z : A) :
    r (R.add (R.sub y x) (R.sub z y)) (R.sub z x) := by
  exact R.trans (R.add_comm (R.sub y x) (R.sub z y))
    (R.trans (R.add_congr (R.refl (R.sub z y)) (R.sub_eq_add_neg y x))
      (R.trans (R.symm (R.add_assoc (R.sub z y) y (R.neg x)))
        (R.trans
          (R.add_congr (sub_add_cancel_right_arg R y z) (R.refl (R.neg x)))
          (R.symm (R.sub_eq_add_neg z x)))))

private theorem add_four_interchange (R : RelCommRing A r)
    (a b c d : A) :
    r (R.add (R.add a b) (R.add c d))
      (R.add (R.add a c) (R.add b d)) := by
  have inner :
      r (R.add b (R.add c d)) (R.add c (R.add b d)) := by
    exact R.trans (R.symm (R.add_assoc b c d))
      (R.trans (R.add_congr (R.add_comm b c) (R.refl d))
        (R.add_assoc c b d))
  exact R.trans (R.add_assoc a b (R.add c d))
    (R.trans (R.add_congr (R.refl a) inner)
      (R.symm (R.add_assoc a c (R.add b d))))

theorem abelPointStepBalance (R : RelCommRing A r)
    (point next : AbelPoint A) :
    r
      (R.add (pointWeightDifferenceTerm R point next)
        (pointNextWeightDifferenceTerm R point next))
      (pointProductJump R point next) := by
  have leftJump :
      r (pointWeightDifferenceTerm R point next)
        (R.sub (R.mul point.1 next.2) (R.mul point.1 point.2)) :=
    mul_sub_right R point.1 next.2 point.2
  have rightRaw :
      r (pointNextWeightDifferenceTerm R point next)
        (R.sub (R.mul next.2 next.1) (R.mul next.2 point.1)) :=
    mul_sub_right R next.2 next.1 point.1
  have rightJump :
      r (pointNextWeightDifferenceTerm R point next)
        (R.sub (pointProduct R next) (R.mul point.1 next.2)) :=
    R.trans rightRaw
      (sub_congr R (R.mul_comm next.2 next.1)
        (R.mul_comm next.2 point.1))
  exact R.trans (R.add_congr leftJump rightJump)
    (sub_chain R (pointProduct R point) (R.mul point.1 next.2)
      (pointProduct R next))

theorem abelByPartsBalanceFrom (R : RelCommRing A r) :
    forall (start : AbelPoint A) (tail : List (AbelPoint A)),
      r
        (R.add
          (listSum R (pointWeightDifferenceTermsFrom R start tail))
          (listSum R (pointNextWeightDifferenceTermsFrom R start tail)))
        (R.sub (pointProduct R (finalPoint start tail)) (pointProduct R start))
  | start, [] => by
      change r (R.add R.zero R.zero)
        (R.sub (pointProduct R start) (pointProduct R start))
      exact R.trans (R.zero_add R.zero)
        (R.symm (sub_self_zero R (pointProduct R start)))
  | start, next :: tail => by
      have ih :
          r
            (R.add
              (listSum R (pointWeightDifferenceTermsFrom R next tail))
              (listSum R (pointNextWeightDifferenceTermsFrom R next tail)))
            (R.sub (pointProduct R (finalPoint next tail))
              (pointProduct R next)) :=
        abelByPartsBalanceFrom R next tail
      have reorder :
          r
            (R.add
              (R.add (pointWeightDifferenceTerm R start next)
                (listSum R (pointWeightDifferenceTermsFrom R next tail)))
              (R.add (pointNextWeightDifferenceTerm R start next)
                (listSum R (pointNextWeightDifferenceTermsFrom R next tail))))
            (R.add
              (R.add (pointWeightDifferenceTerm R start next)
                (pointNextWeightDifferenceTerm R start next))
              (R.add
                (listSum R (pointWeightDifferenceTermsFrom R next tail))
                (listSum R
                  (pointNextWeightDifferenceTermsFrom R next tail)))) :=
        add_four_interchange R
          (pointWeightDifferenceTerm R start next)
          (listSum R (pointWeightDifferenceTermsFrom R next tail))
          (pointNextWeightDifferenceTerm R start next)
          (listSum R (pointNextWeightDifferenceTermsFrom R next tail))
      have replaceParts :
          r
            (R.add
              (R.add (pointWeightDifferenceTerm R start next)
                (pointNextWeightDifferenceTerm R start next))
              (R.add
                (listSum R (pointWeightDifferenceTermsFrom R next tail))
                (listSum R
                  (pointNextWeightDifferenceTermsFrom R next tail))))
            (R.add (pointProductJump R start next)
              (R.sub (pointProduct R (finalPoint next tail))
                (pointProduct R next))) :=
        R.add_congr (abelPointStepBalance R start next) ih
      have collapse :
          r
            (R.add (pointProductJump R start next)
              (R.sub (pointProduct R (finalPoint next tail))
                (pointProduct R next)))
            (R.sub (pointProduct R (finalPoint next tail))
              (pointProduct R start)) := by
        unfold pointProductJump
        exact sub_chain R (pointProduct R start) (pointProduct R next)
          (pointProduct R (finalPoint next tail))
      exact R.trans reorder (R.trans replaceParts collapse)

theorem abelByPartsIdentityFrom (R : RelCommRing A r)
    (start : AbelPoint A) (tail : List (AbelPoint A)) :
    r
      (listSum R (pointWeightDifferenceTermsFrom R start tail))
      (R.sub
        (R.sub (pointProduct R (finalPoint start tail)) (pointProduct R start))
        (listSum R (pointNextWeightDifferenceTermsFrom R start tail))) :=
  eq_sub_of_add_eq R (abelByPartsBalanceFrom R start tail)

theorem abelSummationBalanceFrom (R : RelCommRing A r) :
    forall (prior : A) (rows : List (AbelRow A)),
      r
        (R.add (weightedTermSum R rows)
          (R.add (R.mul prior (firstWeight R.zero rows))
            (forwardDifferenceSumFrom R prior rows)))
        (terminalProduct R prior rows)
  | prior, [] => by
      change
        r (R.add R.zero (R.add (R.mul prior R.zero) R.zero))
          (R.mul prior R.zero)
      exact R.trans (R.zero_add (R.add (R.mul prior R.zero) R.zero))
        (R.add_zero (R.mul prior R.zero))
  | prior, row :: [] => by
      unfold weightedTermSum rowProduct firstWeight forwardDifferenceSumFrom
        terminalProduct prefixAfter lastWeight listSum
      rw [List.map_cons, List.map_nil]
      change
        r
          (R.add (R.add (R.mul row.1 row.2) R.zero)
            (R.add (R.mul prior row.2) R.zero))
          (R.mul (R.add prior row.1) row.2)
      exact R.trans
        (R.add_congr (R.add_zero (R.mul row.1 row.2))
          (R.add_zero (R.mul prior row.2)))
        (prefix_mul_balance R prior row.1 row.2)
  | prior, row :: next :: rows => by
      let current := R.add prior row.1
      have ih :
          r
            (R.add (weightedTermSum R (next :: rows))
              (R.add (R.mul current (firstWeight R.zero (next :: rows)))
                (forwardDifferenceSumFrom R current (next :: rows))))
            (terminalProduct R current (next :: rows)) :=
        abelSummationBalanceFrom R current (next :: rows)
      have head :
          r
            (R.add (R.mul row.1 row.2)
              (R.add (R.mul prior row.2)
                (R.mul current (R.sub next.2 row.2))))
            (R.mul current next.2) := by
        exact head_forward_balance R prior row.1 row.2 next.2
      have reordered :
          r
            (R.add
              (R.add (R.mul row.1 row.2)
                (weightedTermSum R (next :: rows)))
              (R.add (R.mul prior row.2)
                (R.add (R.mul current (R.sub next.2 row.2))
                  (forwardDifferenceSumFrom R current (next :: rows)))))
            (R.add (weightedTermSum R (next :: rows))
              (R.add
                (R.add (R.mul row.1 row.2)
                  (R.add (R.mul prior row.2)
                    (R.mul current (R.sub next.2 row.2))))
                (forwardDifferenceSumFrom R current (next :: rows)))) :=
        add_five_rebracket R
          (R.mul row.1 row.2)
          (weightedTermSum R (next :: rows))
          (R.mul prior row.2)
          (R.mul current (R.sub next.2 row.2))
          (forwardDifferenceSumFrom R current (next :: rows))
      have replaceHead :
          r
            (R.add (weightedTermSum R (next :: rows))
              (R.add
                (R.add (R.mul row.1 row.2)
                  (R.add (R.mul prior row.2)
                    (R.mul current (R.sub next.2 row.2))))
                (forwardDifferenceSumFrom R current (next :: rows))))
            (R.add (weightedTermSum R (next :: rows))
              (R.add (R.mul current next.2)
                (forwardDifferenceSumFrom R current (next :: rows)))) :=
        R.add_congr (R.refl (weightedTermSum R (next :: rows)))
          (R.add_congr head
            (R.refl (forwardDifferenceSumFrom R current (next :: rows))))
      exact R.trans reordered (R.trans replaceHead ih)

theorem abelPartialSummationBalance (R : RelCommRing A r)
    (rows : List (AbelRow A)) :
    r
      (R.add (weightedTermSum R rows)
        (forwardDifferenceSumFrom R R.zero rows))
      (terminalProduct R R.zero rows) := by
  have entryDelta :
      r
        (R.add (R.mul R.zero (firstWeight R.zero rows))
          (forwardDifferenceSumFrom R R.zero rows))
        (forwardDifferenceSumFrom R R.zero rows) := by
    exact R.trans
      (R.add_congr (R.zero_mul (firstWeight R.zero rows))
        (R.refl (forwardDifferenceSumFrom R R.zero rows)))
      (R.zero_add (forwardDifferenceSumFrom R R.zero rows))
  have expand :
      r
        (R.add (weightedTermSum R rows)
          (forwardDifferenceSumFrom R R.zero rows))
        (R.add (weightedTermSum R rows)
          (R.add (R.mul R.zero (firstWeight R.zero rows))
            (forwardDifferenceSumFrom R R.zero rows))) :=
    R.add_congr (R.refl (weightedTermSum R rows)) (R.symm entryDelta)
  exact R.trans expand (abelSummationBalanceFrom R R.zero rows)

theorem abelPartialSummationIdentity (R : RelCommRing A r)
    (rows : List (AbelRow A)) :
    r (weightedTermSum R rows) (abelPartialSummationRight R rows) := by
  unfold abelPartialSummationRight
  exact eq_sub_of_add_eq R (abelPartialSummationBalance R rows)

theorem abelDiscreteIntegralProductBalance (R : RelCommRing A r)
    (rows : List (AbelRow A)) :
    r
      (R.add (weightedTermSum R rows)
        (forwardDifferenceSumFrom R R.zero rows))
      (terminalProduct R R.zero rows) :=
  abelPartialSummationBalance R rows

theorem abelPartialSumIdentity (R : RelCommRing A r)
    (rows : List (AbelRow A)) :
    r (weightedTermSum R rows) (abelPartialSummationRight R rows) :=
  abelPartialSummationIdentity R rows

private theorem ratNum_zero_to_RatEq_zero_local {x : BEDC.Derived.RationalUp.RatNum} :
    BEDC.Derived.RationalUp.IntEq x.num BEDC.Derived.RationalUp.intZero ->
      BEDC.Derived.RationalUp.RatEq x BEDC.Derived.RationalUp.ratZero := by
  intro numZero
  unfold BEDC.Derived.RationalUp.RatEq
  change
    BEDC.Derived.RationalUp.IntEq
      (BEDC.Derived.RationalUp.IntMul x.num
        (BEDC.Derived.RationalUp.ratDenInt BEDC.Derived.RationalUp.ratZero))
      (BEDC.Derived.RationalUp.IntMul BEDC.Derived.RationalUp.ratZero.num
        (BEDC.Derived.RationalUp.ratDenInt x))
  have leftToZero :
      BEDC.Derived.RationalUp.IntEq
        (BEDC.Derived.RationalUp.IntMul x.num
          (BEDC.Derived.RationalUp.ratDenInt BEDC.Derived.RationalUp.ratZero))
        BEDC.Derived.RationalUp.intZero :=
    BEDC.Derived.RationalUp.IntEq_trans
      (BEDC.Derived.RationalUp.intMul_left_congr (c := x.num)
        BEDC.Derived.RationalUp.ratDenInt_zero)
      (BEDC.Derived.RationalUp.IntEq_trans
        (BEDC.Derived.RationalUp.intMul_one_right x.num) numZero)
  have rightToZero :
      BEDC.Derived.RationalUp.IntEq
        (BEDC.Derived.RationalUp.IntMul BEDC.Derived.RationalUp.ratZero.num
          (BEDC.Derived.RationalUp.ratDenInt x))
        BEDC.Derived.RationalUp.intZero := by
    change BEDC.Derived.RationalUp.IntEq
      (BEDC.Derived.RationalUp.IntMul BEDC.Derived.RationalUp.intZero
        (BEDC.Derived.RationalUp.ratDenInt x))
      BEDC.Derived.RationalUp.intZero
    exact BEDC.Derived.RationalUp.intMul_zero_left
      (BEDC.Derived.RationalUp.ratDenInt x)
  exact BEDC.Derived.RationalUp.IntEq_trans leftToZero
    (BEDC.Derived.RationalUp.IntEq_symm rightToZero)

private theorem ratMul_zero_left_for_ring
    (x : BEDC.Derived.RationalUp.RatNum) :
    BEDC.Derived.RationalUp.RatEq
      (BEDC.Derived.RationalUp.ratMul BEDC.Derived.RationalUp.ratZero x)
      BEDC.Derived.RationalUp.ratZero := by
  apply ratNum_zero_to_RatEq_zero_local
  unfold BEDC.Derived.RationalUp.ratMul BEDC.Derived.RationalUp.ratZero
    BEDC.Derived.RationalUp.intToRat
  change BEDC.Derived.RationalUp.IntEq
    (BEDC.Derived.RationalUp.IntMul BEDC.Derived.RationalUp.intZero x.num)
    BEDC.Derived.RationalUp.intZero
  exact BEDC.Derived.RationalUp.intMul_zero_left x.num

private theorem ratMul_zero_right_for_ring
    (x : BEDC.Derived.RationalUp.RatNum) :
    BEDC.Derived.RationalUp.RatEq
      (BEDC.Derived.RationalUp.ratMul x BEDC.Derived.RationalUp.ratZero)
      BEDC.Derived.RationalUp.ratZero := by
  exact BEDC.Derived.RationalUp.RatEq_trans _ _ _
    (BEDC.Derived.RationalUp.ratMul_comm x BEDC.Derived.RationalUp.ratZero)
    (ratMul_zero_left_for_ring x)

def ratNumRing :
    RelCommRing BEDC.Derived.RationalUp.RatNum BEDC.Derived.RationalUp.RatEq where
  zero := BEDC.Derived.RationalUp.ratZero
  one := BEDC.Derived.RationalUp.ratOne
  add := BEDC.Derived.RationalUp.ratAdd
  mul := BEDC.Derived.RationalUp.ratMul
  neg := BEDC.Derived.RationalUp.ratNeg
  refl := BEDC.Derived.RationalUp.RatEq_refl
  symm := by
    intro x y
    exact BEDC.Derived.RationalUp.RatEq_symm
  trans := by
    intro x y z
    exact BEDC.Derived.RationalUp.RatEq_trans x y z
  add_congr := by
    intro x x' y y'
    exact BEDC.Derived.RationalUp.ratAdd_respects
  mul_congr := by
    intro x x' y y'
    exact BEDC.Derived.RationalUp.ratMul_respects
  neg_congr := by
    intro x y
    exact BEDC.Derived.RationalUp.ratNeg_respects
  add_assoc := BEDC.Derived.LocatedReal.ratAdd_assoc_local
  add_comm := BEDC.Derived.RationalUp.ratAdd_comm
  add_zero := BEDC.Derived.RationalUp.ratAdd_zero_right
  zero_add := BEDC.Derived.RationalUp.ratZero_add_left
  add_neg := BEDC.Derived.LocatedReal.ratAdd_neg_local
  neg_add := BEDC.Derived.LocatedReal.ratNeg_add_local
  mul_assoc := BEDC.Derived.RationalUp.ratMul_assoc
  mul_one := BEDC.Derived.RationalUp.ratMul_one_right
  one_mul := BEDC.Derived.RationalUp.ratOne_mul_left
  mul_zero := ratMul_zero_right_for_ring
  zero_mul := ratMul_zero_left_for_ring
  left_distrib := BEDC.Real.RatNumKernel.ratMul_add_left
  right_distrib := BEDC.Real.RatNumKernel.ratMul_add_right
  mul_comm := BEDC.Derived.RationalUp.ratMul_comm

theorem ratNumAbelPartialSummationIdentity
    (rows : List (AbelRow BEDC.Derived.RationalUp.RatNum)) :
    BEDC.Derived.RationalUp.RatEq
      (weightedTermSum ratNumRing rows)
      (abelPartialSummationRight ratNumRing rows) :=
  abelPartialSumIdentity ratNumRing rows

theorem ratNumAbelByPartsIdentityFrom
    (start : AbelPoint BEDC.Derived.RationalUp.RatNum)
    (tail : List (AbelPoint BEDC.Derived.RationalUp.RatNum)) :
    BEDC.Derived.RationalUp.RatEq
      (listSum ratNumRing
        (pointWeightDifferenceTermsFrom ratNumRing start tail))
      (ratNumRing.sub
        (ratNumRing.sub
          (pointProduct ratNumRing (finalPoint start tail))
          (pointProduct ratNumRing start))
        (listSum ratNumRing
          (pointNextWeightDifferenceTermsFrom ratNumRing start tail))) :=
  abelByPartsIdentityFrom ratNumRing start tail

abbrev Z : Type := BEDC.Algebra.Rel.IntegerUp
abbrev Zeq : Z -> Z -> Prop := BEDC.Algebra.Rel.IntEq

def integerRing : RelCommRing Z Zeq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

theorem integerAbelPartialSummationIdentity
    (rows : List (AbelRow Z)) :
    Zeq (weightedTermSum integerRing rows)
      (abelPartialSummationRight integerRing rows) :=
  abelPartialSummationIdentity integerRing rows

theorem abelSummationMobiusUnitPair
    (rows : List (AbelRow Z)) :
    Zeq (weightedTermSum integerRing rows)
        (abelPartialSummationRight integerRing rows) ∧
      BEDC.Derived.DirichletRingUp.ArithmeticFnEq
        (BEDC.Derived.DirichletRingUp.dirichletConvolution
          BEDC.Derived.DirichletRingUp.dirichletMobius
          BEDC.Derived.DirichletRingUp.dirichletOne)
        BEDC.Derived.DirichletRingUp.dirichletEpsilon := by
  constructor
  · exact integerAbelPartialSummationIdentity rows
  · exact BEDC.Derived.DirichletRingUp.mobius_mul_one_eq_epsilon

end BEDC.Derived.AbelSummationUp
