import BEDC.Algebra.FiniteFold
import BEDC.Derived.DirichletRingUp
import BEDC.Derived.IntUp.CommRing

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
