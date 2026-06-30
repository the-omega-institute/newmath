import BEDC.Derived.FibonacciUp
import BEDC.Derived.LucasSequenceGeneralUp
import BEDC.Derived.Window6Doubling

namespace BEDC.Derived.FibonacciLucasIdentitiesUp

abbrev fib : Nat -> Nat :=
  BEDC.Derived.FibonacciUp.fib

abbrev lucas : Nat -> Nat :=
  BEDC.Derived.FibonacciUp.lucas

abbrev altSign : Nat -> Int :=
  BEDC.Derived.FibonacciUp.altSign

theorem fib_zero : fib 0 = 0 :=
  BEDC.Derived.FibonacciUp.fib_zero

theorem fib_one : fib 1 = 1 :=
  BEDC.Derived.FibonacciUp.fib_one

theorem lucas_zero : lucas 0 = 2 :=
  BEDC.Derived.FibonacciUp.lucas_zero

theorem lucas_one : lucas 1 = 1 :=
  BEDC.Derived.FibonacciUp.lucas_one

theorem lucas_succ_eq_fib_add (n : Nat) :
    lucas (n + 1) = fib n + fib (n + 2) := by
  change BEDC.Derived.FibonacciUp.lucas (n + 1) =
    BEDC.Derived.FibonacciUp.fib n + BEDC.Derived.FibonacciUp.fib (n + 2)
  rw [BEDC.Derived.FibonacciUp.lucas_eq_fib_add n]
  exact Nat.add_comm (fib (n + 2)) (fib n)

theorem lucas_succ_eq_fib_add_commuted (n : Nat) :
    lucas (n + 1) = fib (n + 2) + fib n :=
  BEDC.Derived.FibonacciUp.lucas_eq_fib_add n

theorem lucas_eq_fib_pred_add_succ (n : Nat) :
    lucas (n + 1) = fib n + fib (n + 2) :=
  lucas_succ_eq_fib_add n

theorem lucas_eq_fib_succ_add_pred (n : Nat) :
    lucas (n + 1) = fib (n + 2) + fib n :=
  lucas_succ_eq_fib_add_commuted n

private theorem add_right_rotation (a b c d : Nat) :
    a + b + (c + d) = (a + c) + (b + d) := by
  rw [Nat.add_assoc]
  rw [← Nat.add_assoc b c d]
  rw [Nat.add_comm b c]
  rw [Nat.add_assoc c b d]
  rw [Nat.add_assoc a c (b + d)]

private theorem add_mul_pure (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  induction c with
  | zero =>
      rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ c ih =>
      calc
        (a + b) * Nat.succ c =
            (a + b) * c + (a + b) := Nat.mul_succ (a + b) c
        _ = (a * c + b * c) + (a + b) :=
          congrArg (fun x => x + (a + b)) ih
        _ = a * c + (b * c + (a + b)) :=
          Nat.add_assoc (a * c) (b * c) (a + b)
        _ = a * c + ((b * c + a) + b) :=
          congrArg (fun x => a * c + x) (Nat.add_assoc (b * c) a b).symm
        _ = a * c + ((a + b * c) + b) :=
          congrArg (fun x => a * c + (x + b)) (Nat.add_comm (b * c) a)
        _ = a * c + (a + (b * c + b)) :=
          congrArg (fun x => a * c + x) (Nat.add_assoc a (b * c) b)
        _ = (a * c + a) + (b * c + b) :=
          (Nat.add_assoc (a * c) a (b * c + b)).symm
        _ = a * Nat.succ c + (b * c + b) :=
          congrArg (fun x => x + (b * c + b)) (Nat.mul_succ a c).symm
        _ = a * Nat.succ c + b * Nat.succ c :=
          congrArg (fun x => a * Nat.succ c + x) (Nat.mul_succ b c).symm

private theorem fib_pair_step (a0 a1 b0 b1 : Nat) :
    ((a1 + a0) * b1 + a1 * b0) + (a1 * b1 + a0 * b0) =
      ((a1 + a0) + a1) * b1 + (a1 + a0) * b0 := by
  calc
    ((a1 + a0) * b1 + a1 * b0) + (a1 * b1 + a0 * b0) =
        (((a1 + a0) * b1 + a1 * b1) + (a1 * b0 + a0 * b0)) := by
      rw [add_right_rotation]
    _ = (((a1 + a0) + a1) * b1 + (a1 * b0 + a0 * b0)) := by
      rw [(add_mul_pure (a1 + a0) a1 b1).symm]
    _ = (((a1 + a0) + a1) * b1 + (a1 + a0) * b0) := by
      rw [(add_mul_pure a1 a0 b0).symm]

structure GoldenPhiPair where
  const : Nat
  phiCoeff : Nat

private theorem golden_phi_pair_eq {x y : GoldenPhiPair}
    (hconst : x.const = y.const) (hphi : x.phiCoeff = y.phiCoeff) : x = y := by
  cases x with
  | mk xconst xphi =>
      cases y with
      | mk yconst yphi =>
          cases hconst
          cases hphi
          rfl

def goldenPhiMul (x y : GoldenPhiPair) : GoldenPhiPair :=
  ⟨x.const * y.const + x.phiCoeff * y.phiCoeff,
    x.const * y.phiCoeff + x.phiCoeff * y.const + x.phiCoeff * y.phiCoeff⟩

def goldenPhi : GoldenPhiPair :=
  ⟨0, 1⟩

def goldenPhiPow : Nat -> GoldenPhiPair
  | 0 => ⟨1, 0⟩
  | n + 1 => goldenPhiMul (goldenPhiPow n) goldenPhi

theorem golden_phi_power_zero :
    goldenPhiPow 0 = ⟨1, 0⟩ := by
  rfl

theorem golden_phi_power_one :
    goldenPhiPow 1 = ⟨0, 1⟩ := by
  rfl

private theorem goldenPhiMul_right_phi (a b : Nat) :
    goldenPhiMul ⟨a, b⟩ goldenPhi = ⟨b, a + b⟩ := by
  apply golden_phi_pair_eq
  · change a * 0 + b * 1 = b
    rw [Nat.mul_zero, Nat.mul_one, Nat.zero_add]
  · change a * 1 + b * 0 + b * 1 = a + b
    rw [Nat.mul_one, Nat.mul_zero, Nat.mul_one, Nat.add_zero]

theorem golden_phi_power_pair (n : Nat) :
    goldenPhiPow (n + 1) = ⟨fib n, fib (n + 1)⟩ := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change goldenPhiMul (goldenPhiPow (n + 1)) goldenPhi =
        ⟨fib (n + 1), fib (n + 1 + 1)⟩
      calc
        goldenPhiMul (goldenPhiPow (n + 1)) goldenPhi =
            goldenPhiMul ⟨fib n, fib (n + 1)⟩ goldenPhi := by
          rw [ih]
        _ = ⟨fib (n + 1), fib n + fib (n + 1)⟩ :=
          goldenPhiMul_right_phi (fib n) (fib (n + 1))
        _ = ⟨fib (n + 1), fib (n + 1 + 1)⟩ := by
          apply golden_phi_pair_eq
          · rfl
          · change fib n + fib (n + 1) = fib (n + 1) + fib n
            exact Nat.add_comm (fib n) (fib (n + 1))

theorem fib_add_pair (m n : Nat) :
    fib (m + n + 1) =
        fib (m + 1) * fib (n + 1) + fib m * fib n ∧
      fib (m + n + 2) =
        fib (m + 2) * fib (n + 1) + fib (m + 1) * fib n := by
  induction m with
  | zero =>
      constructor
      · rw [Nat.zero_add]
        change fib (n + 1) = 1 * fib (n + 1) + 0 * fib n
        rw [Nat.one_mul]
        rw [Nat.zero_mul]
        exact (Nat.add_zero (fib (n + 1))).symm
      · rw [Nat.zero_add]
        change fib (n + 2) = 1 * fib (n + 1) + 1 * fib n
        rw [Nat.one_mul]
        rw [Nat.one_mul]
        rfl
  | succ m ih =>
      constructor
      · rw [show m + 1 + n + 1 = m + n + 2 by
          rw [Nat.add_assoc m 1 n]
          rw [Nat.add_comm 1 n]
          rw [← Nat.add_assoc m n 1]]
        change fib (m + n + 2) =
          fib (m + 2) * fib (n + 1) + fib (m + 1) * fib n
        exact ih.right
      · calc
          fib (m + 1 + n + 2) =
              fib (m + n + 3) := by
            rw [show m + 1 + n + 2 = m + n + 3 by
              rw [Nat.add_assoc m 1 n]
              rw [Nat.add_comm 1 n]
              rw [← Nat.add_assoc m n 1]]
          _ = fib (m + n + 2) + fib (m + n + 1) := by
            rfl
          _ =
              (fib (m + 2) * fib (n + 1) + fib (m + 1) * fib n) +
                (fib (m + 1) * fib (n + 1) + fib m * fib n) := by
            rw [ih.left, ih.right]
          _ =
              fib (m + 1 + 2) * fib (n + 1) +
                fib (m + 1 + 1) * fib n := by
            change ((fib (m + 1) + fib m) * fib (n + 1) +
                fib (m + 1) * fib n) +
                (fib (m + 1) * fib (n + 1) + fib m * fib n) =
              ((fib (m + 1) + fib m) + fib (m + 1)) * fib (n + 1) +
                (fib (m + 1) + fib m) * fib n
            exact fib_pair_step (fib m) (fib (m + 1)) (fib n) (fib (n + 1))

theorem fib_addition_succ (m n : Nat) :
    fib (m + n + 1) =
      fib (m + 1) * fib (n + 1) + fib m * fib n :=
  (fib_add_pair m n).left

theorem fib_shifted_addition (m n : Nat) :
    fib ((m + 1) + n) =
      fib (m + 1) * fib (n + 1) + fib m * fib n := by
  rw [show (m + 1) + n = m + n + 1 by
    rw [Nat.add_assoc m 1 n]
    rw [Nat.add_comm 1 n]
    rw [← Nat.add_assoc m n 1]]
  exact fib_addition_succ m n

theorem fib_addition_pred_succ (m n : Nat) :
    fib ((m + 1) + n) =
      fib (m + 1) * fib (n + 1) + fib m * fib n :=
  fib_shifted_addition m n

theorem fib_addition_pred_succ_strong (m n : Nat) :
    fib ((m + 1) + n) =
      fib (m + 1) * fib (n + 1) + fib m * fib n :=
  Nat.strongRecOn m
    (motive := fun k =>
      fib ((k + 1) + n) =
        fib (k + 1) * fib (n + 1) + fib k * fib n)
    (fun k _previous => fib_addition_pred_succ k n)

theorem fib_two_mul_eq_fib_mul_lucas (n : Nat) :
    fib (2 * n) = fib n * lucas n :=
  BEDC.Derived.Window6Doubling.fib_two_mul_eq_fib_mul_lucas n

theorem fib_double_eq_fib_mul_lucas (n : Nat) :
    fib (2 * n) = fib n * lucas n :=
  fib_two_mul_eq_fib_mul_lucas n

theorem lucas_fib_norm_identity (n : Nat) :
    ((lucas n : Int)) ^ 2 - 5 * ((fib n : Int)) ^ 2 =
      4 * altSign n :=
  BEDC.Derived.Window6LucasFibNormRelation.lucas_fib_norm_universal n

theorem lucas_square_sub_five_fib_square_eq_four_altSign (n : Nat) :
    ((lucas n : Int)) ^ 2 - 5 * ((fib n : Int)) ^ 2 =
      4 * altSign n :=
  lucas_fib_norm_identity n

theorem lucas_sequence_norm_identity (n : Nat) :
    BEDC.Derived.LucasSequenceGeneralUp.lucasNorm 1 (-1) n =
      4 * BEDC.Derived.LucasSequenceGeneralUp.qpow (-1) n :=
  BEDC.Derived.LucasSequenceGeneralUp.fibonacci_norm_identity n

theorem catalan_gap_one_cassini_orientation (n : Nat) :
    (((fib (n + 2) * fib n : Nat) : Int) -
      ((fib (n + 1) * fib (n + 1) : Nat) : Int)) =
      altSign (n + 1) :=
  BEDC.Derived.FibonacciUp.cassini_shifted n

theorem catalan_gap_one_identity (n : Nat) :
    (((fib (n + 2) * fib n : Nat) : Int) -
      ((fib (n + 1) * fib (n + 1) : Nat) : Int)) =
      altSign (n + 1) :=
  catalan_gap_one_cassini_orientation n

theorem docagne_gap_one (n : Nat) :
    (((fib (n + 2) * fib n : Nat) : Int) -
      ((fib (n + 1) * fib (n + 1) : Nat) : Int)) =
      altSign (n + 1) :=
  catalan_gap_one_cassini_orientation n

end BEDC.Derived.FibonacciLucasIdentitiesUp
