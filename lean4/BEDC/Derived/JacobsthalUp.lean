import BEDC.Derived.LucasSequenceUp

namespace BEDC.Derived.JacobsthalUp

def jacobsthal : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => jacobsthal (n + 1) + 2 * jacobsthal n

def jacobsthalLucas : Nat -> Nat
  | 0 => 2
  | 1 => 1
  | n + 2 => jacobsthalLucas (n + 1) + 2 * jacobsthalLucas n

def powTwo : Nat -> Nat
  | 0 => 1
  | n + 1 => 2 * powTwo n

def altSign : Nat -> Bool
  | 0 => true
  | n + 1 => not (altSign n)

def closedNumerNat (n : Nat) : Nat :=
  3 * jacobsthal n

abbrev jacobsthalInt (n : Nat) : Int :=
  (jacobsthal n : Int)

abbrev closedNumerInt (n : Nat) : Int :=
  (closedNumerNat n : Int)

abbrev lucasUJacobsthal (n : Nat) : Int :=
  BEDC.Derived.LucasSequenceUp.lucasU 1 (-2) n

abbrev lucasVJacobsthal (n : Nat) : Int :=
  BEDC.Derived.LucasSequenceUp.lucasV 1 (-2) n

private def twoStep (motive : Nat -> Prop)
    (zeroCase : motive 0)
    (oneCase : motive 1)
    (stepCase : ∀ n, motive n -> motive (n + 1) -> motive (n + 2)) :
    ∀ n, motive n
  | 0 => zeroCase
  | 1 => oneCase
  | n + 2 =>
      stepCase n
        (twoStep motive zeroCase oneCase stepCase n)
        (twoStep motive zeroCase oneCase stepCase (n + 1))

private theorem nat_mul_assoc_clean (a b c : Nat) :
    (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      calc
        (a * b) * Nat.succ c = (a * b) * c + a * b := Nat.mul_succ (a * b) c
        _ = a * (b * c) + a * b := congrArg (fun x => x + a * b) ih
        _ = a * (b * c + b) := (Nat.mul_add a (b * c) b).symm
        _ = a * (b * Nat.succ c) := congrArg (fun x => a * x) (Nat.mul_succ b c).symm

private theorem scale_step_nat (a b : Nat) :
    3 * (a + 2 * b) = 3 * a + 2 * (3 * b) := by
  calc
    3 * (a + 2 * b) = 3 * a + 3 * (2 * b) := Nat.left_distrib 3 a (2 * b)
    _ = 3 * a + (3 * 2) * b := by
      rw [nat_mul_assoc_clean]
    _ = 3 * a + (2 * 3) * b := by
      rfl
    _ = 3 * a + 2 * (3 * b) := by
      rw [nat_mul_assoc_clean]

theorem jacobsthal_zero :
    jacobsthal 0 = 0 := by
  rfl

theorem jacobsthal_one :
    jacobsthal 1 = 1 := by
  rfl

theorem jacobsthal_recurrence (n : Nat) :
    jacobsthal (n + 2) = jacobsthal (n + 1) + 2 * jacobsthal n := by
  rfl

theorem jacobsthalLucas_zero :
    jacobsthalLucas 0 = 2 := by
  rfl

theorem jacobsthalLucas_one :
    jacobsthalLucas 1 = 1 := by
  rfl

theorem jacobsthalLucas_recurrence (n : Nat) :
    jacobsthalLucas (n + 2) =
      jacobsthalLucas (n + 1) + 2 * jacobsthalLucas n := by
  rfl

theorem powTwo_zero :
    powTwo 0 = 1 := by
  rfl

theorem powTwo_succ (n : Nat) :
    powTwo (n + 1) = 2 * powTwo n := by
  rfl

theorem altSign_zero :
    altSign 0 = true := by
  rfl

theorem altSign_succ (n : Nat) :
    altSign (n + 1) = not (altSign n) := by
  rfl

theorem closedNumerNat_def (n : Nat) :
    closedNumerNat n = 3 * jacobsthal n := by
  rfl

theorem closedNumerNat_zero :
    closedNumerNat 0 = 0 := by
  rfl

theorem closedNumerNat_one :
    closedNumerNat 1 = 3 := by
  rfl

theorem closedNumerNat_recurrence (n : Nat) :
    closedNumerNat (n + 2) =
      closedNumerNat (n + 1) + 2 * closedNumerNat n := by
  unfold closedNumerNat
  rw [jacobsthal_recurrence]
  exact scale_step_nat (jacobsthal (n + 1)) (jacobsthal n)

theorem jacobsthal_closed_form_scaled_nat (n : Nat) :
    closedNumerNat n = 3 * jacobsthal n := by
  rfl

theorem jacobsthal_closed_form_divides (n : Nat) :
    ∃ q : Nat, closedNumerNat n = 3 * q :=
  Exists.intro (jacobsthal n) (jacobsthal_closed_form_scaled_nat n)

theorem jacobsthal_closed_form_scaled_int (n : Nat) :
    closedNumerInt n = 3 * jacobsthalInt n := by
  unfold closedNumerInt closedNumerNat jacobsthalInt
  change ((3 * jacobsthal n : Nat) : Int) = 3 * ((jacobsthal n : Nat) : Int)
  exact (Int.ofNat_mul_ofNat 3 (jacobsthal n)).symm

private theorem neg_mul_neg_two (x : Int) :
    -((-2 : Int) * x) = 2 * x := by
  cases x with
  | ofNat n =>
      induction n with
      | zero =>
          rfl
      | succ n _ =>
          rfl
  | negSucc n =>
      induction n with
      | zero =>
          rfl
      | succ n _ =>
          rfl

private theorem lucas_jacobsthal_step (x y : Int) :
    (1 : Int) * x - (-2 : Int) * y = x + 2 * y := by
  rw [Int.one_mul]
  rw [Int.sub_eq_add_neg]
  rw [neg_mul_neg_two y]

theorem lucasUJacobsthal_zero :
    lucasUJacobsthal 0 = 0 := by
  rfl

theorem lucasUJacobsthal_one :
    lucasUJacobsthal 1 = 1 := by
  rfl

theorem lucasUJacobsthal_recurrence (n : Nat) :
    lucasUJacobsthal (n + 2) =
      lucasUJacobsthal (n + 1) + 2 * lucasUJacobsthal n := by
  exact lucas_jacobsthal_step
    (lucasUJacobsthal (n + 1)) (lucasUJacobsthal n)

theorem lucasVJacobsthal_zero :
    lucasVJacobsthal 0 = 2 := by
  rfl

theorem lucasVJacobsthal_one :
    lucasVJacobsthal 1 = 1 := by
  rfl

theorem lucasVJacobsthal_recurrence (n : Nat) :
    lucasVJacobsthal (n + 2) =
      lucasVJacobsthal (n + 1) + 2 * lucasVJacobsthal n := by
  exact lucas_jacobsthal_step
    (lucasVJacobsthal (n + 1)) (lucasVJacobsthal n)

theorem lucasUJacobsthal_eq_jacobsthalInt_zero :
    lucasUJacobsthal 0 = jacobsthalInt 0 := by
  rfl

theorem lucasUJacobsthal_eq_jacobsthalInt_one :
    lucasUJacobsthal 1 = jacobsthalInt 1 := by
  rfl

end BEDC.Derived.JacobsthalUp
