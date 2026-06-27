import BEDC.Algebra.FiniteFold
import BEDC.Algebra.Rel.IntegerUp
import BEDC.Derived.ContFracUp
import BEDC.Derived.MatrixUp
import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.ContinuantUp

open BEDC.Algebra.Rel

namespace Rel

variable {A : Type u} {r : A -> A -> Prop}
variable (R : RelCommRing A r)

abbrev ConvergentState := BEDC.Derived.ContFracUp.ConvergentState A

def continuant (coeffs : List A) : A :=
  (BEDC.Derived.ContFracUp.Rel.convergentStateOfList R coeffs).curr.p

def continuantPrev (coeffs : List A) : A :=
  (BEDC.Derived.ContFracUp.Rel.convergentStateOfList R coeffs).prev.p

def continuantDenominator (coeffs : List A) : A :=
  (BEDC.Derived.ContFracUp.Rel.convergentStateOfList R coeffs).curr.q

def continuantPrevDenominator (coeffs : List A) : A :=
  (BEDC.Derived.ContFracUp.Rel.convergentStateOfList R coeffs).prev.q

def ratioDenominator : List A -> A
  | [] => R.zero
  | _x :: tail => continuant R tail

structure ContinuantRatio where
  numerator : A
  denominator : A

def continuantRatio (coeffs : List A) : ContinuantRatio (A := A) :=
  { numerator := continuant R coeffs
    denominator := ratioDenominator R coeffs }

theorem convergentStateFrom_append
    (s : ConvergentState) :
    ∀ xs ys : List A,
      BEDC.Derived.ContFracUp.Rel.convergentStateFrom R s (xs ++ ys) =
        BEDC.Derived.ContFracUp.Rel.convergentStateFrom R
          (BEDC.Derived.ContFracUp.Rel.convergentStateFrom R s xs) ys
  | [], _ys => rfl
  | x :: xs, ys =>
      convergentStateFrom_append
        (s := BEDC.Derived.ContFracUp.Rel.convergentStep R x s)
        xs ys

theorem continuant_nil :
    r (continuant R []) R.one :=
  R.refl R.one

theorem continuant_singleton (x : A) :
    r (continuant R [x]) x := by
  unfold continuant BEDC.Derived.ContFracUp.Rel.convergentStateOfList
  unfold BEDC.Derived.ContFracUp.Rel.convergentStateFrom
  unfold BEDC.Derived.ContFracUp.Rel.convergentStep
  unfold BEDC.Derived.ContFracUp.Rel.initialConvergentState
  exact R.trans (R.add_congr (R.mul_one x) (R.refl R.zero)) (R.add_zero x)

theorem continuantPrev_snoc (coeffs : List A) (x : A) :
    r (continuantPrev R (coeffs ++ [x])) (continuant R coeffs) := by
  unfold continuantPrev continuant BEDC.Derived.ContFracUp.Rel.convergentStateOfList
  rw [convergentStateFrom_append]
  exact R.refl
    (BEDC.Derived.ContFracUp.Rel.convergentStateFrom R
      (BEDC.Derived.ContFracUp.Rel.initialConvergentState R) coeffs).curr.p

theorem continuant_snoc (coeffs : List A) (x : A) :
    r (continuant R (coeffs ++ [x]))
      (R.add (R.mul x (continuant R coeffs)) (continuantPrev R coeffs)) := by
  unfold continuant continuantPrev BEDC.Derived.ContFracUp.Rel.convergentStateOfList
  rw [convergentStateFrom_append]
  exact R.refl
    (R.add
      (R.mul x
        (BEDC.Derived.ContFracUp.Rel.convergentStateFrom R
          (BEDC.Derived.ContFracUp.Rel.initialConvergentState R) coeffs).curr.p)
      (BEDC.Derived.ContFracUp.Rel.convergentStateFrom R
        (BEDC.Derived.ContFracUp.Rel.initialConvergentState R) coeffs).prev.p)

private theorem denominator_p_alignment_step
    (a : A) (s t : ConvergentState) :
    r s.curr.q t.curr.p ->
      r s.prev.q t.prev.p ->
        r
            (BEDC.Derived.ContFracUp.Rel.convergentStep R a s).curr.q
            (BEDC.Derived.ContFracUp.Rel.convergentStep R a t).curr.p ∧
          r
            (BEDC.Derived.ContFracUp.Rel.convergentStep R a s).prev.q
            (BEDC.Derived.ContFracUp.Rel.convergentStep R a t).prev.p := by
  intro sameCurr samePrev
  unfold BEDC.Derived.ContFracUp.Rel.convergentStep
  exact ⟨R.add_congr (R.mul_congr (R.refl a) sameCurr) samePrev, sameCurr⟩

private theorem denominator_p_alignment_from
    (s t : ConvergentState) :
    r s.curr.q t.curr.p ->
      r s.prev.q t.prev.p ->
        ∀ coeffs : List A,
          r
              (BEDC.Derived.ContFracUp.Rel.convergentStateFrom R s coeffs).curr.q
              (BEDC.Derived.ContFracUp.Rel.convergentStateFrom R t coeffs).curr.p ∧
            r
              (BEDC.Derived.ContFracUp.Rel.convergentStateFrom R s coeffs).prev.q
              (BEDC.Derived.ContFracUp.Rel.convergentStateFrom R t coeffs).prev.p
  | sameCurr, samePrev, [] => ⟨sameCurr, samePrev⟩
  | sameCurr, samePrev, a :: tail =>
      let stepSame := denominator_p_alignment_step R a s t sameCurr samePrev
      denominator_p_alignment_from
        (s := BEDC.Derived.ContFracUp.Rel.convergentStep R a s)
        (t := BEDC.Derived.ContFracUp.Rel.convergentStep R a t)
        stepSame.left stepSame.right tail

private theorem head_step_q_matches_initial_p (x : A) :
    r
        (BEDC.Derived.ContFracUp.Rel.convergentStep R x
          (BEDC.Derived.ContFracUp.Rel.initialConvergentState R)).curr.q
        (BEDC.Derived.ContFracUp.Rel.initialConvergentState R).curr.p ∧
      r
        (BEDC.Derived.ContFracUp.Rel.convergentStep R x
          (BEDC.Derived.ContFracUp.Rel.initialConvergentState R)).prev.q
        (BEDC.Derived.ContFracUp.Rel.initialConvergentState R).prev.p := by
  unfold BEDC.Derived.ContFracUp.Rel.convergentStep
  unfold BEDC.Derived.ContFracUp.Rel.initialConvergentState
  exact
    ⟨R.trans (R.add_congr (R.mul_zero x) (R.refl R.one)) (R.zero_add R.one),
      R.refl R.zero⟩

theorem convergent_numerator_eq_continuant (coeffs : List A) :
    r
      (BEDC.Derived.ContFracUp.Rel.convergentStateOfList R coeffs).curr.p
      (continuant R coeffs) :=
  R.refl (continuant R coeffs)

theorem convergent_denominator_cons (x : A) (tail : List A) :
    r (continuantDenominator R (x :: tail)) (continuant R tail) := by
  unfold continuantDenominator continuant
  unfold BEDC.Derived.ContFracUp.Rel.convergentStateOfList
  let start := BEDC.Derived.ContFracUp.Rel.initialConvergentState R
  have head := head_step_q_matches_initial_p R x
  exact (denominator_p_alignment_from R
    (BEDC.Derived.ContFracUp.Rel.convergentStep R x start) start
    head.left head.right tail).left

theorem convergent_as_continuant_ratio (coeffs : List A) :
    r
        (BEDC.Derived.ContFracUp.Rel.convergentStateOfList R coeffs).curr.p
        (continuantRatio R coeffs).numerator ∧
      r
        (BEDC.Derived.ContFracUp.Rel.convergentStateOfList R coeffs).curr.q
        (continuantRatio R coeffs).denominator := by
  cases coeffs with
  | nil =>
      exact ⟨R.refl R.one, R.refl R.zero⟩
  | cons x tail =>
      exact ⟨R.refl (continuant R (x :: tail)), convergent_denominator_cons R x tail⟩

theorem continuant_euler_identity (coeffs : List A) :
    r
      (R.add
        (R.mul (continuant R coeffs) (continuantPrevDenominator R coeffs))
        (R.neg (R.mul (continuantPrev R coeffs) (continuantDenominator R coeffs))))
      (BEDC.Derived.ContFracUp.Rel.alternatingOne R coeffs.length) := by
  unfold continuant continuantPrev continuantDenominator continuantPrevDenominator
  exact BEDC.Derived.ContFracUp.Rel.contFracConvergents_det R coeffs

end Rel

abbrev IntegerUp := BEDC.Algebra.Rel.IntegerUp
abbrev IntEq := BEDC.Algebra.Rel.IntEq
abbrev intZero := BEDC.Algebra.Rel.intZero
abbrev intOne := BEDC.Algebra.Rel.intOne
abbrev IntAdd := BEDC.Algebra.Rel.IntAdd
abbrev IntMul := BEDC.Algebra.Rel.IntMul
abbrev IntNeg := BEDC.Algebra.Rel.IntNeg

private abbrev integerRing : RelCommRing IntegerUp IntEq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

def integerContinuant (coeffs : List IntegerUp) : IntegerUp :=
  Rel.continuant integerRing coeffs

def integerContinuantPrev (coeffs : List IntegerUp) : IntegerUp :=
  Rel.continuantPrev integerRing coeffs

def integerContinuantDenominator (coeffs : List IntegerUp) : IntegerUp :=
  Rel.continuantDenominator integerRing coeffs

def integerContinuantPrevDenominator (coeffs : List IntegerUp) : IntegerUp :=
  Rel.continuantPrevDenominator integerRing coeffs

def integerContinuantRatio (coeffs : List IntegerUp) :
    Rel.ContinuantRatio (A := IntegerUp) :=
  Rel.continuantRatio integerRing coeffs

def partialCoefficientMatrix (x : IntegerUp) : BEDC.Derived.MatrixUp.Mat2 :=
  { a00 := x
    a01 := intOne
    a10 := intOne
    a11 := intZero }

def matrixOfConvergentState
    (s : BEDC.Derived.ContFracUp.ConvergentState IntegerUp) :
    BEDC.Derived.MatrixUp.Mat2 :=
  { a00 := s.curr.p
    a01 := s.prev.p
    a10 := s.curr.q
    a11 := s.prev.q }

def convergentMatrix (coeffs : List IntegerUp) : BEDC.Derived.MatrixUp.Mat2 :=
  matrixOfConvergentState
    (BEDC.Derived.ContFracUp.Rel.convergentStateOfList integerRing coeffs)

def continuantMatrixProductFrom
    (M : BEDC.Derived.MatrixUp.Mat2) : List IntegerUp -> BEDC.Derived.MatrixUp.Mat2
  | [] => M
  | x :: tail =>
      continuantMatrixProductFrom
        (BEDC.Derived.MatrixUp.matMul M (partialCoefficientMatrix x)) tail

def continuantMatrixProduct (coeffs : List IntegerUp) : BEDC.Derived.MatrixUp.Mat2 :=
  continuantMatrixProductFrom BEDC.Derived.MatrixUp.matOne coeffs

private theorem int_mul_one_add_mul_zero (x y : IntegerUp) :
    IntEq (IntAdd (IntMul x intOne) (IntMul y intZero)) x := by
  exact integerRing.trans
    (integerRing.add_congr (integerRing.mul_one x) (integerRing.mul_zero y))
    (integerRing.add_zero x)

private theorem matrix_step_eq_convergentStep
    (s : BEDC.Derived.ContFracUp.ConvergentState IntegerUp) (x : IntegerUp) :
    BEDC.Derived.MatrixUp.MatEq
      (BEDC.Derived.MatrixUp.matMul (matrixOfConvergentState s) (partialCoefficientMatrix x))
      (matrixOfConvergentState
        (BEDC.Derived.ContFracUp.Rel.convergentStep integerRing x s)) := by
  unfold BEDC.Derived.MatrixUp.MatEq
  unfold BEDC.Derived.MatrixUp.matMul partialCoefficientMatrix matrixOfConvergentState
  unfold BEDC.Derived.ContFracUp.Rel.convergentStep
  exact
    ⟨integerRing.add_congr
        (integerRing.mul_comm s.curr.p x)
        (integerRing.mul_one s.prev.p),
      int_mul_one_add_mul_zero s.curr.p s.prev.p,
      integerRing.add_congr
        (integerRing.mul_comm s.curr.q x)
        (integerRing.mul_one s.prev.q),
      int_mul_one_add_mul_zero s.curr.q s.prev.q⟩

private theorem continuantMatrixProductFrom_respects
    {M N : BEDC.Derived.MatrixUp.Mat2} :
    BEDC.Derived.MatrixUp.MatEq M N ->
      ∀ coeffs : List IntegerUp,
        BEDC.Derived.MatrixUp.MatEq
          (continuantMatrixProductFrom M coeffs)
          (continuantMatrixProductFrom N coeffs)
  | same, [] => same
  | same, x :: tail =>
      continuantMatrixProductFrom_respects
        (M := BEDC.Derived.MatrixUp.matMul M (partialCoefficientMatrix x))
        (N := BEDC.Derived.MatrixUp.matMul N (partialCoefficientMatrix x))
        (BEDC.Derived.MatrixUp.matMul_respects same
          (BEDC.Derived.MatrixUp.MatEq_refl (partialCoefficientMatrix x)))
        tail

private theorem continuantMatrixProductFrom_eq_state
    (s : BEDC.Derived.ContFracUp.ConvergentState IntegerUp) :
    ∀ coeffs : List IntegerUp,
      BEDC.Derived.MatrixUp.MatEq
        (continuantMatrixProductFrom (matrixOfConvergentState s) coeffs)
        (matrixOfConvergentState
          (BEDC.Derived.ContFracUp.Rel.convergentStateFrom integerRing s coeffs))
  | [] => BEDC.Derived.MatrixUp.MatEq_refl (matrixOfConvergentState s)
  | x :: tail =>
      BEDC.Derived.MatrixUp.MatEq_trans
        (continuantMatrixProductFrom_respects
          (M := BEDC.Derived.MatrixUp.matMul
            (matrixOfConvergentState s) (partialCoefficientMatrix x))
          (N := matrixOfConvergentState
            (BEDC.Derived.ContFracUp.Rel.convergentStep integerRing x s))
          (matrix_step_eq_convergentStep s x)
          tail)
        (continuantMatrixProductFrom_eq_state
          (BEDC.Derived.ContFracUp.Rel.convergentStep integerRing x s) tail)

theorem continuantMatrixProduct_eq_convergentMatrix (coeffs : List IntegerUp) :
    BEDC.Derived.MatrixUp.MatEq
      (continuantMatrixProduct coeffs)
      (convergentMatrix coeffs) := by
  unfold continuantMatrixProduct convergentMatrix
  unfold BEDC.Derived.ContFracUp.Rel.convergentStateOfList
  exact continuantMatrixProductFrom_eq_state
    (BEDC.Derived.ContFracUp.Rel.initialConvergentState integerRing) coeffs

theorem integer_convergent_as_continuant_ratio (coeffs : List IntegerUp) :
    IntEq
        (BEDC.Derived.ContFracUp.integerConvergentStateOfList coeffs).curr.p
        (integerContinuantRatio coeffs).numerator ∧
      IntEq
        (BEDC.Derived.ContFracUp.integerConvergentStateOfList coeffs).curr.q
        (integerContinuantRatio coeffs).denominator := by
  exact Rel.convergent_as_continuant_ratio integerRing coeffs

theorem integer_continuant_euler_identity (coeffs : List IntegerUp) :
    IntEq
      (IntAdd
        (IntMul (integerContinuant coeffs) (integerContinuantPrevDenominator coeffs))
        (IntNeg (IntMul (integerContinuantPrev coeffs) (integerContinuantDenominator coeffs))))
      (BEDC.Derived.ContFracUp.Rel.alternatingOne integerRing coeffs.length) := by
  exact Rel.continuant_euler_identity integerRing coeffs

end BEDC.Derived.ContinuantUp
