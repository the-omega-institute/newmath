import BEDC.Derived.TribonacciUp
import BEDC.Derived.IntUp.CommRingCore

namespace BEDC.Derived.TribonacciMatrixUp

open BEDC.Derived.TribonacciUp
open BEDC.Derived.IntUp
open BEDC.Derived.RationalUp
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

abbrev State3 := BEDC.Derived.TribonacciUp.State3

abbrev Mat3 := BEDC.Derived.TribonacciUp.Mat3

def tribonacciSeed : State3 :=
  ⟨1, 1, 0⟩

def tribonacciMatrix : Mat3 :=
  ⟨1, 1, 1,
    1, 0, 0,
    0, 1, 0⟩

def identityMatrix : Mat3 :=
  ⟨1, 0, 0,
    0, 1, 0,
    0, 0, 1⟩

def matVec (M : Mat3) (v : State3) : State3 :=
  ⟨M.aa * v.top + M.ab * v.middle + M.ac * v.bottom,
    M.ba * v.top + M.bb * v.middle + M.bc * v.bottom,
    M.ca * v.top + M.cb * v.middle + M.cc * v.bottom⟩

def matMul (A B : Mat3) : Mat3 :=
  ⟨A.aa * B.aa + A.ab * B.ba + A.ac * B.ca,
    A.aa * B.ab + A.ab * B.bb + A.ac * B.cb,
    A.aa * B.ac + A.ab * B.bc + A.ac * B.cc,
    A.ba * B.aa + A.bb * B.ba + A.bc * B.ca,
    A.ba * B.ab + A.bb * B.bb + A.bc * B.cb,
    A.ba * B.ac + A.bb * B.bc + A.bc * B.cc,
    A.ca * B.aa + A.cb * B.ba + A.cc * B.ca,
    A.ca * B.ab + A.cb * B.bb + A.cc * B.cb,
    A.ca * B.ac + A.cb * B.bc + A.cc * B.cc⟩

def matPow (M : Mat3) : Nat -> Mat3
  | 0 => identityMatrix
  | n + 1 => matMul M (matPow M n)

def tribonacciMatrixPow (n : Nat) : Mat3 :=
  matPow tribonacciMatrix n

def trace (M : Mat3) : Nat :=
  M.aa + M.bb + M.cc

def detPositive (M : Mat3) : Nat :=
  M.aa * M.bb * M.cc + M.ab * M.bc * M.ca + M.ac * M.ba * M.cb

def detNegative (M : Mat3) : Nat :=
  M.ac * M.bb * M.ca + M.ab * M.ba * M.cc + M.aa * M.bc * M.cb

def detPair (M : Mat3) : BHist × BHist :=
  (natToUnary (detPositive M), natToUnary (detNegative M))

def detInt (M : Mat3) : BEDC.Derived.PrimeUp.IntegerUp :=
  pairToInt (detPair M)

private theorem state3_eq {x y : State3}
    (htop : x.top = y.top) (hmiddle : x.middle = y.middle)
    (hbottom : x.bottom = y.bottom) :
    x = y := by
  cases x with
  | mk top middle bottom =>
      cases y with
      | mk top' middle' bottom' =>
          cases htop
          cases hmiddle
          cases hbottom
          rfl

private theorem mat3_eq {A B : Mat3}
    (haa : A.aa = B.aa) (hab : A.ab = B.ab) (hac : A.ac = B.ac)
    (hba : A.ba = B.ba) (hbb : A.bb = B.bb) (hbc : A.bc = B.bc)
    (hca : A.ca = B.ca) (hcb : A.cb = B.cb) (hcc : A.cc = B.cc) :
    A = B := by
  cases A with
  | mk aa ab ac ba bb bc ca cb cc =>
      cases B with
      | mk aa' ab' ac' ba' bb' bc' ca' cb' cc' =>
          cases haa
          cases hab
          cases hac
          cases hba
          cases hbb
          cases hbc
          cases hca
          cases hcb
          cases hcc
          rfl

private theorem add_three_reverse (a b c : Nat) :
    a + b + c = c + b + a := by
  calc
    a + b + c = c + (a + b) := by
      rw [Nat.add_comm (a + b) c]
    _ = c + (b + a) := by
      rw [Nat.add_comm a b]
    _ = c + b + a := by
      rw [Nat.add_assoc]

private theorem add_middle (ca ab bb cb : Nat) :
    ca + (ab + bb + cb) = ab + bb + (ca + cb) := by
  calc
    ca + (ab + bb + cb)
        = ca + (ab + (bb + cb)) := by
          rw [Nat.add_assoc ab bb cb]
    _ = ab + (ca + (bb + cb)) := by
          rw [Nat.add_left_comm ca ab (bb + cb)]
    _ = ab + (bb + (ca + cb)) := by
          rw [Nat.add_left_comm ca bb cb]
    _ = ab + bb + (ca + cb) := by
          rw [← Nat.add_assoc ab bb (ca + cb)]

private theorem add_two_blocks (aa ba ca ab bb cb : Nat) :
    aa + ba + ca + (ab + bb + cb) =
      aa + ab + (ba + bb) + (ca + cb) := by
  calc
    aa + ba + ca + (ab + bb + cb)
        = aa + ba + (ca + (ab + bb + cb)) := by
          rw [Nat.add_assoc (aa + ba) ca (ab + bb + cb)]
    _ = aa + ba + (ab + bb + (ca + cb)) := by
          rw [add_middle ca ab bb cb]
    _ = aa + (ba + (ab + bb + (ca + cb))) := by
          rw [Nat.add_assoc aa ba (ab + bb + (ca + cb))]
    _ = aa + (ab + (ba + (bb + (ca + cb)))) := by
          rw [Nat.add_assoc ab bb (ca + cb)]
          rw [Nat.add_left_comm ba ab (bb + (ca + cb))]
    _ = aa + (ab + ((ba + bb) + (ca + cb))) := by
          rw [← Nat.add_assoc ba bb (ca + cb)]
    _ = aa + ab + ((ba + bb) + (ca + cb)) := by
          rw [← Nat.add_assoc aa ab ((ba + bb) + (ca + cb))]
    _ = aa + ab + (ba + bb) + (ca + cb) := by
          rw [← Nat.add_assoc (aa + ab) (ba + bb) (ca + cb)]

private theorem tribonacciMatrix_vec_step (v : State3) :
    matVec tribonacciMatrix v = stepState v := by
  cases v with
  | mk top middle bottom =>
      apply state3_eq
      · change 1 * top + 1 * middle + 1 * bottom =
          top + middle + bottom
        rw [Nat.one_mul, Nat.one_mul, Nat.one_mul]
      · change 1 * top + 0 * middle + 0 * bottom = top
        rw [Nat.one_mul, Nat.zero_mul, Nat.zero_mul]
        exact (Nat.add_zero (top + 0)).trans (Nat.add_zero top)
      · change 0 * top + 1 * middle + 0 * bottom = middle
        rw [Nat.zero_mul, Nat.one_mul, Nat.zero_mul]
        exact (congrArg (fun x => x + 0) (Nat.zero_add middle)).trans
          (Nat.add_zero middle)

private theorem identity_vec (v : State3) :
    matVec identityMatrix v = v := by
  cases v with
  | mk top middle bottom =>
      apply state3_eq
      · change 1 * top + 0 * middle + 0 * bottom = top
        rw [Nat.one_mul, Nat.zero_mul, Nat.zero_mul]
        exact (Nat.add_zero (top + 0)).trans (Nat.add_zero top)
      · change 0 * top + 1 * middle + 0 * bottom = middle
        rw [Nat.zero_mul, Nat.one_mul, Nat.zero_mul]
        exact (congrArg (fun x => x + 0) (Nat.zero_add middle)).trans
          (Nat.add_zero middle)
      · change 0 * top + 0 * middle + 1 * bottom = bottom
        rw [Nat.zero_mul, Nat.zero_mul, Nat.one_mul]
        exact (congrArg (fun x => x + bottom) (Nat.zero_add 0)).trans
          (Nat.zero_add bottom)

private theorem tribonacciMatrix_mul_vec_seed (P : Mat3) :
    matVec (matMul tribonacciMatrix P) tribonacciSeed =
      matVec tribonacciMatrix (matVec P tribonacciSeed) := by
  cases P with
  | mk aa ab ac ba bb bc ca cb cc =>
      apply state3_eq
      · unfold matVec matMul tribonacciMatrix tribonacciSeed
        dsimp
        change ((1 * aa + 1 * ba + 1 * ca) * 1 +
            (1 * ab + 1 * bb + 1 * cb) * 1 +
              (1 * ac + 1 * bc + 1 * cc) * 0) =
          1 * (aa * 1 + ab * 1 + ac * 0) +
            1 * (ba * 1 + bb * 1 + bc * 0) +
              1 * (ca * 1 + cb * 1 + cc * 0)
        repeat rw [Nat.one_mul]
        repeat rw [Nat.mul_one]
        repeat rw [Nat.mul_zero]
        repeat rw [Nat.add_zero]
        exact add_two_blocks aa ba ca ab bb cb
      · unfold matVec matMul tribonacciMatrix tribonacciSeed
        dsimp
        repeat rw [Nat.one_mul]
        repeat rw [Nat.zero_mul]
        repeat rw [Nat.mul_one]
        repeat rw [Nat.mul_zero]
        repeat rw [Nat.add_zero]
      · unfold matVec matMul tribonacciMatrix tribonacciSeed
        dsimp
        repeat rw [Nat.one_mul]
        repeat rw [Nat.zero_mul]
        repeat rw [Nat.mul_one]
        repeat rw [Nat.mul_zero]
        repeat rw [Nat.add_zero]
        repeat rw [Nat.zero_add]

theorem tribonacciMatrix_pow_seed_state (n : Nat) :
    matVec (tribonacciMatrixPow n) tribonacciSeed = state n := by
  induction n with
  | zero =>
      exact identity_vec tribonacciSeed
  | succ n ih =>
      change matVec (matMul tribonacciMatrix (matPow tribonacciMatrix n))
          tribonacciSeed = state (n + 1)
      rw [tribonacciMatrix_mul_vec_seed]
      change matVec tribonacciMatrix
        (matVec (tribonacciMatrixPow n) tribonacciSeed) = state (n + 1)
      rw [ih, tribonacciMatrix_vec_step]
      rfl

theorem tribonacciMatrix_pow_seed (n : Nat) :
    matVec (tribonacciMatrixPow n) tribonacciSeed =
      ⟨tribonacci (n + 2), tribonacci (n + 1), tribonacci n⟩ := by
  exact BEDC.Derived.TribonacciUp.tribonacci_strong_induction
    (P := fun k : Nat =>
      matVec (tribonacciMatrixPow k) tribonacciSeed =
        ⟨tribonacci (k + 2), tribonacci (k + 1), tribonacci k⟩)
    (by rfl)
    (by rfl)
    (by rfl)
    (fun k _prev _next twoAhead => by
      change matVec (matMul tribonacciMatrix (matPow tribonacciMatrix (k + 2)))
          tribonacciSeed =
        State3.mk (tribonacci (k + 3 + 2)) (tribonacci (k + 3 + 1))
          (tribonacci (k + 3))
      rw [tribonacciMatrix_mul_vec_seed]
      change matVec tribonacciMatrix
          (matVec (tribonacciMatrixPow (k + 2)) tribonacciSeed) =
        State3.mk (tribonacci (k + 3 + 2)) (tribonacci (k + 3 + 1))
          (tribonacci (k + 3))
      rw [twoAhead, tribonacciMatrix_vec_step]
      change
        State3.mk
          (tribonacci (k + 2 + 2) + tribonacci (k + 2 + 1) +
            tribonacci (k + 2))
          (tribonacci (k + 2 + 2)) (tribonacci (k + 2 + 1)) =
        State3.mk (tribonacci (k + 3 + 2)) (tribonacci (k + 3 + 1))
          (tribonacci (k + 3))
      apply state3_eq
      · exact (add_three_reverse
          (tribonacci (k + 2 + 2)) (tribonacci (k + 2 + 1))
          (tribonacci (k + 2))).trans
          (BEDC.Derived.TribonacciUp.tribonacci_sum_identity (k + 2))
      · rfl
      · rfl)
    n

theorem tribonacciMatrix_pow_top (n : Nat) :
    (matVec (tribonacciMatrixPow n) tribonacciSeed).top =
      tribonacci (n + 2) := by
  rw [tribonacciMatrix_pow_seed]

theorem tribonacciMatrix_pow_middle (n : Nat) :
    (matVec (tribonacciMatrixPow n) tribonacciSeed).middle =
      tribonacci (n + 1) := by
  rw [tribonacciMatrix_pow_seed]

theorem tribonacciMatrix_pow_bottom (n : Nat) :
    (matVec (tribonacciMatrixPow n) tribonacciSeed).bottom =
      tribonacci n := by
  rw [tribonacciMatrix_pow_seed]

theorem tribonacciMatrix_trace :
    trace tribonacciMatrix = 1 := by
  rfl

theorem tribonacciMatrix_det_pair :
    detPair tribonacciMatrix = (natToUnary 1, natToUnary 0) := by
  rfl

theorem tribonacciMatrix_det_pair_carrier :
    IntPairCarrier (detPair tribonacciMatrix).1 (detPair tribonacciMatrix).2 := by
  rw [tribonacciMatrix_det_pair]
  exact ⟨natToUnary_unary 1, natToUnary_unary 0⟩

theorem tribonacciMatrix_det_is_one :
    IntPairClassifier (intToPair (detInt tribonacciMatrix))
      (natToUnary 1, natToUnary 0) := by
  unfold detInt
  rw [tribonacciMatrix_det_pair]
  exact intToPair_pairToInt_classifier (natToUnary 1, natToUnary 0)
    ⟨natToUnary_unary 1, natToUnary_unary 0⟩

theorem tribonacci_sum_from_matrix_row (n : Nat) :
    (matVec tribonacciMatrix
      (matVec (tribonacciMatrixPow n) tribonacciSeed)).top =
        tribonacci (n + 3) := by
  rw [tribonacciMatrix_pow_seed]
  change 1 * tribonacci (n + 2) + 1 * tribonacci (n + 1) +
      1 * tribonacci n =
    tribonacci (n + 3)
  rw [Nat.one_mul, Nat.one_mul, Nat.one_mul]
  exact (add_three_reverse
    (tribonacci (n + 2)) (tribonacci (n + 1)) (tribonacci n)).trans
      (BEDC.Derived.TribonacciUp.tribonacci_sum_identity n)

theorem tribonacciMatrix_one_step_identity (n : Nat) :
    tribonacci (n + 3) =
      tribonacci n + tribonacci (n + 1) + tribonacci (n + 2) := by
  exact BEDC.Derived.TribonacciUp.tribonacci_recurrence n

end BEDC.Derived.TribonacciMatrixUp
