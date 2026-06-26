import BEDC.Algebra.Rel.IntegerUp
import BEDC.Derived.GcdUp

namespace BEDC.Derived.ContFracUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.PrimeUp
open BEDC.Derived.PadicUp
open BEDC.Algebra.Rel

structure ConvergentPair (A : Type u) where
  p : A
  q : A

structure ConvergentState (A : Type u) where
  prev : ConvergentPair A
  curr : ConvergentPair A

namespace Rel

variable {A : Type u} {r : A -> A -> Prop}
variable (R : RelCommRing A r)

def initialConvergentState : ConvergentState A :=
  { prev := { p := R.zero, q := R.one }
    curr := { p := R.one, q := R.zero } }

def convergentStep (a : A) (s : ConvergentState A) : ConvergentState A :=
  { prev := s.curr
    curr :=
      { p := R.add (R.mul a s.curr.p) s.prev.p
        q := R.add (R.mul a s.curr.q) s.prev.q } }

def convergentStateFrom : ConvergentState A -> List A -> ConvergentState A
  | s, [] => s
  | s, a :: tail => convergentStateFrom (convergentStep R a s) tail

def convergentStateOfList (coeffs : List A) : ConvergentState A :=
  convergentStateFrom R (initialConvergentState R) coeffs

def convergentDet (s : ConvergentState A) : A :=
  R.add (R.mul s.curr.p s.prev.q) (R.neg (R.mul s.prev.p s.curr.q))

def alternatingFrom : Nat -> A -> A
  | 0, x => x
  | n + 1, x => alternatingFrom n (R.neg x)

def alternatingOne (n : Nat) : A :=
  alternatingFrom R n R.one

private theorem add_four_swap (a b c d : A) :
    r (R.add (R.add a b) (R.add c d))
      (R.add (R.add a c) (R.add b d)) := by
  exact R.trans (R.add_assoc a b (R.add c d))
    (R.trans
      (R.add_congr (R.refl a) (R.symm (R.add_assoc b c d)))
      (R.trans
        (R.add_congr (R.refl a)
          (R.add_congr (R.add_comm b c) (R.refl d)))
        (R.trans
          (R.add_congr (R.refl a) (R.add_assoc c b d))
          (R.symm (R.add_assoc a c (R.add b d))))))

private theorem neg_add (a b : A) :
    r (R.neg (R.add a b)) (R.add (R.neg a) (R.neg b)) := by
  have paired :
      r (R.add (R.add a b) (R.add (R.neg a) (R.neg b)))
        (R.add (R.add a (R.neg a)) (R.add b (R.neg b))) :=
    add_four_swap R a b (R.neg a) (R.neg b)
  have collapsed :
      r (R.add (R.add a (R.neg a)) (R.add b (R.neg b)))
        (R.add R.zero R.zero) :=
    R.add_congr (R.add_neg a) (R.add_neg b)
  have zeroed :
      r (R.add (R.add a b) (R.add (R.neg a) (R.neg b))) R.zero :=
    R.trans paired (R.trans collapsed (R.zero_add R.zero))
  exact R.symm (R.eq_neg_of_add_eq_zero zeroed)

private theorem sub_common_left {x x' y z : A} :
    r x x' ->
      r (R.add (R.add x y) (R.neg (R.add x' z)))
        (R.add y (R.neg z)) := by
  intro sameCommon
  have negExpand :
      r (R.add (R.add x y) (R.neg (R.add x' z)))
        (R.add (R.add x y) (R.add (R.neg x') (R.neg z))) :=
    R.add_congr (R.refl (R.add x y)) (neg_add R x' z)
  have commonAligned :
      r (R.add (R.add x y) (R.add (R.neg x') (R.neg z)))
        (R.add (R.add x y) (R.add (R.neg x) (R.neg z))) :=
    R.add_congr (R.refl (R.add x y))
      (R.add_congr (R.neg_congr (R.symm sameCommon)) (R.refl (R.neg z)))
  have paired :
      r (R.add (R.add x y) (R.add (R.neg x) (R.neg z)))
        (R.add (R.add x (R.neg x)) (R.add y (R.neg z))) :=
    add_four_swap R x y (R.neg x) (R.neg z)
  have collapsed :
      r (R.add (R.add x (R.neg x)) (R.add y (R.neg z)))
        (R.add R.zero (R.add y (R.neg z))) :=
    R.add_congr (R.add_neg x) (R.refl (R.add y (R.neg z)))
  exact R.trans negExpand
    (R.trans commonAligned
      (R.trans paired (R.trans collapsed (R.zero_add (R.add y (R.neg z))))))

private theorem sub_swap_add_zero (x y : A) :
    r (R.add (R.add x (R.neg y)) (R.add y (R.neg x))) R.zero := by
  have reorder :
      r (R.add (R.add x (R.neg y)) (R.add y (R.neg x)))
        (R.add (R.add x (R.neg y)) (R.add (R.neg x) y)) :=
    R.add_congr (R.refl (R.add x (R.neg y))) (R.add_comm y (R.neg x))
  have paired :
      r (R.add (R.add x (R.neg y)) (R.add (R.neg x) y))
        (R.add (R.add x (R.neg x)) (R.add (R.neg y) y)) :=
    add_four_swap R x (R.neg y) (R.neg x) y
  have collapsed :
      r (R.add (R.add x (R.neg x)) (R.add (R.neg y) y))
        (R.add R.zero R.zero) :=
    R.add_congr (R.add_neg x) (R.neg_add y)
  exact R.trans reorder (R.trans paired (R.trans collapsed (R.zero_add R.zero)))

private theorem step_common_product (a p q : A) :
    r (R.mul (R.mul a p) q) (R.mul p (R.mul a q)) := by
  exact R.trans (R.mul_assoc a p q)
    (R.trans
      (R.mul_congr (R.refl a) (R.mul_comm p q))
      (R.trans
        (R.symm (R.mul_assoc a q p))
        (R.mul_comm (R.mul a q) p)))

theorem convergentStep_det (a : A) (s : ConvergentState A) :
    r (convergentDet R (convergentStep R a s))
      (R.neg (convergentDet R s)) := by
  cases s with
  | mk prev curr =>
      cases prev with
      | mk p0 q0 =>
          cases curr with
          | mk p1 q1 =>
              unfold convergentDet convergentStep
              have leftExpand :
                  r (R.mul (R.add (R.mul a p1) p0) q1)
                    (R.add (R.mul (R.mul a p1) q1) (R.mul p0 q1)) :=
                R.right_distrib (R.mul a p1) p0 q1
              have rightExpand :
                  r (R.mul p1 (R.add (R.mul a q1) q0))
                    (R.add (R.mul p1 (R.mul a q1)) (R.mul p1 q0)) :=
                R.left_distrib p1 (R.mul a q1) q0
              have expanded :
                  r
                    (R.add (R.mul (R.add (R.mul a p1) p0) q1)
                      (R.neg (R.mul p1 (R.add (R.mul a q1) q0))))
                    (R.add
                      (R.add (R.mul (R.mul a p1) q1) (R.mul p0 q1))
                      (R.neg (R.add (R.mul p1 (R.mul a q1)) (R.mul p1 q0)))) :=
                R.add_congr leftExpand (R.neg_congr rightExpand)
              have commonCancelled :
                  r
                    (R.add
                      (R.add (R.mul (R.mul a p1) q1) (R.mul p0 q1))
                      (R.neg (R.add (R.mul p1 (R.mul a q1)) (R.mul p1 q0))))
                    (R.add (R.mul p0 q1) (R.neg (R.mul p1 q0))) :=
                sub_common_left R (step_common_product R a p1 q1)
              have reverseIsNeg :
                  r (R.add (R.mul p0 q1) (R.neg (R.mul p1 q0)))
                    (R.neg (R.add (R.mul p1 q0) (R.neg (R.mul p0 q1)))) :=
                R.eq_neg_of_add_eq_zero
                  (sub_swap_add_zero R (R.mul p1 q0) (R.mul p0 q1))
              exact R.trans expanded (R.trans commonCancelled reverseIsNeg)

private theorem alternatingFrom_respects {x y : A} :
    r x y -> forall n : Nat, r (alternatingFrom R n x) (alternatingFrom R n y) := by
  intro same n
  induction n generalizing x y with
  | zero =>
      exact same
  | succ n ih =>
      exact ih (R.neg_congr same)

theorem convergentStateFrom_det (s : ConvergentState A) (coeffs : List A) :
    r (convergentDet R (convergentStateFrom R s coeffs))
      (alternatingFrom R coeffs.length (convergentDet R s)) := by
  induction coeffs generalizing s with
  | nil =>
      exact R.refl (convergentDet R s)
  | cons a tail ih =>
      exact R.trans (ih (convergentStep R a s))
        (alternatingFrom_respects R (convergentStep_det R a s) tail.length)

theorem initialConvergentState_det :
    r (convergentDet R (initialConvergentState R)) R.one := by
  unfold convergentDet initialConvergentState
  have first :
      r (R.mul R.one R.one) R.one :=
    R.mul_one R.one
  have second :
      r (R.neg (R.mul R.zero R.zero)) R.zero :=
    R.trans (R.neg_congr (R.mul_zero R.zero)) (R.neg_zero)
  exact R.trans (R.add_congr first second) (R.add_zero R.one)

theorem contFracConvergents_det (coeffs : List A) :
    r (convergentDet R (convergentStateOfList R coeffs))
      (alternatingOne R coeffs.length) := by
  unfold convergentStateOfList alternatingOne
  exact R.trans (convergentStateFrom_det R (initialConvergentState R) coeffs)
    (alternatingFrom_respects R (initialConvergentState_det R) coeffs.length)

end Rel

abbrev IntegerUp := BEDC.Algebra.Rel.IntegerUp
abbrev IntEq := BEDC.Algebra.Rel.IntEq

def integerConvergentStateOfList (coeffs : List IntegerUp) : ConvergentState IntegerUp :=
  Rel.convergentStateOfList BEDC.Algebra.Rel.IntegerUp_RelCommRing coeffs

def integerConvergentDet (s : ConvergentState IntegerUp) : IntegerUp :=
  Rel.convergentDet BEDC.Algebra.Rel.IntegerUp_RelCommRing s

theorem integerContFracConvergents_det (coeffs : List IntegerUp) :
    IntEq (integerConvergentDet (integerConvergentStateOfList coeffs))
      (Rel.alternatingOne BEDC.Algebra.Rel.IntegerUp_RelCommRing coeffs.length) :=
  Rel.contFracConvergents_det BEDC.Algebra.Rel.IntegerUp_RelCommRing coeffs

structure EuclidStep where
  dividend : BHist
  divisor : BHist
  quotient : BHist
  remainder : BHist

def EuclidStepValid (s : EuclidStep) : Prop :=
  UnaryHistory s.dividend ∧ UnaryHistory s.divisor ∧
    (hsame s.divisor BHist.Empty -> False) ∧
      NatDivRem s.divisor s.dividend s.quotient s.remainder

def natDivRemStep (a b : BHist) : EuclidStep :=
  { dividend := a
    divisor := b
    quotient := natQuotFn b a
    remainder := natModFn b a }

theorem natDivRemStep_valid {a b : BHist} :
    UnaryHistory a -> UnaryHistory b -> (hsame b BHist.Empty -> False) ->
      EuclidStepValid (natDivRemStep a b) := by
  intro aUnary bUnary bNonempty
  unfold EuclidStepValid natDivRemStep
  exact ⟨aUnary, bUnary, bNonempty, natModFn_spec bUnary aUnary bNonempty⟩

def natEuclidQuotientsFuel : Nat -> BHist -> BHist -> List BHist
  | 0, _a, _b => []
  | _fuel + 1, _a, BHist.Empty => []
  | _fuel + 1, _a, BHist.e0 _tail => []
  | fuel + 1, a, BHist.e1 tail =>
      natQuotFn (BHist.e1 tail) a ::
        natEuclidQuotientsFuel fuel (BHist.e1 tail)
          (natModFn (BHist.e1 tail) a)

def natEuclidQuotients (a b : BHist) : List BHist :=
  natEuclidQuotientsFuel (bwordLength b + 1) a b

theorem natEuclidQuotients_empty_divisor (a : BHist) :
    natEuclidQuotients a BHist.Empty = [] := by
  rfl

theorem natEuclidQuotients_first_step {a tail : BHist} :
    natEuclidQuotientsFuel (Nat.succ (bwordLength (BHist.e1 tail))) a
        (BHist.e1 tail) =
      natQuotFn (BHist.e1 tail) a ::
        natEuclidQuotientsFuel (bwordLength (BHist.e1 tail)) (BHist.e1 tail)
          (natModFn (BHist.e1 tail) a) := by
  rfl

end BEDC.Derived.ContFracUp
