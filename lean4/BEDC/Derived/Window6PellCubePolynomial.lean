namespace BEDC.Derived.Window6PellCubePolynomial

/-- Coefficient-wise addition of two polynomials (index = degree). -/
def padd : List Nat → List Nat → List Nat
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: padd p q

/-- Scalar multiple c · p. -/
def scaleP (c : Nat) : List Nat → List Nat
  | [] => []
  | a :: p => (c * a) :: scaleP c p

/-- Multiply by x (shift coefficients up by one degree). -/
def shiftP (p : List Nat) : List Nat := 0 :: p

/-- Multiply by the linear form (c + x). -/
def addX (c : Nat) (p : List Nat) : List Nat := padd (scaleP c p) (shiftP p)

/-- Pell-graph cube polynomial coefficient sequence. -/
def Q : Nat → List Nat
  | 0 => [1]
  | 1 => [2, 1]
  | n + 2 => padd (addX 2 (Q (n + 1))) (addX 1 (Q n))

/-- Evaluate a coefficient-list polynomial at t (Horner form): eval (a::p) t = a + t * eval p t. -/
def eval : List Nat → Nat → Nat
  | [], _ => 0
  | a :: p, t => a + t * eval p t

theorem Q_zero : Q 0 = [1] := rfl

theorem Q_one : Q 1 = [2, 1] := rfl

theorem Q_two : Q 2 = [5, 5, 1] := rfl

theorem Q_three : Q 3 = [12, 18, 8, 1] := rfl

theorem Q_four : Q 4 = [29, 58, 40, 11, 1] := rfl

theorem Q_five : Q 5 = [70, 175, 164, 71, 14, 1] := rfl

theorem Q_six : Q 6 = [169, 507, 601, 357, 111, 17, 1] := rfl

theorem Q_seven : Q 7 = [408, 1428, 2048, 1550, 664, 160, 20, 1] := rfl

theorem add_pair_rearrange (a b x y : Nat) :
    (a + b) + (x + y) = (a + x) + (b + y) := by
  calc
    (a + b) + (x + y) = a + (b + (x + y)) := by
      rw [Nat.add_assoc]
    _ = a + ((b + x) + y) := by
      rw [← Nat.add_assoc b x y]
    _ = a + ((x + b) + y) := by
      rw [Nat.add_comm b x]
    _ = a + (x + (b + y)) := by
      rw [Nat.add_assoc x b y]
    _ = (a + x) + (b + y) := by
      rw [Nat.add_assoc]

theorem mul_assoc_pure (a b c : Nat) :
    (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      calc
        (a * b) * 0 = 0 := by
          rw [Nat.mul_zero]
        _ = a * (b * 0) := by
          rw [Nat.mul_zero, Nat.mul_zero]
  | succ c ih =>
      calc
        (a * b) * (Nat.succ c) = (a * b) * c + a * b := by
          rw [Nat.mul_succ]
        _ = a * (b * c) + a * b := by
          rw [ih]
        _ = a * (b * c + b) := by
          rw [Nat.mul_add]
        _ = a * (b * Nat.succ c) := by
          rw [Nat.mul_succ]

theorem add_mul_pure (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  induction c with
  | zero =>
      calc
        (a + b) * 0 = 0 := by
          rw [Nat.mul_zero]
        _ = 0 + 0 := by
          rw [Nat.zero_add]
        _ = a * 0 + b * 0 := by
          rw [Nat.mul_zero, Nat.mul_zero]
  | succ c ih =>
      calc
        (a + b) * (Nat.succ c) = (a + b) * c + (a + b) := by
          rw [Nat.mul_succ]
        _ = (a * c + b * c) + (a + b) := by
          rw [ih]
        _ = (a * c + a) + (b * c + b) := by
          rw [add_pair_rearrange]
        _ = a * Nat.succ c + (b * c + b) := by
          rw [← Nat.mul_succ]
        _ = a * Nat.succ c + b * Nat.succ c := by
          rw [← Nat.mul_succ]

theorem eval_padd (p q : List Nat) (t : Nat) :
    eval (padd p q) t = eval p t + eval q t := by
  induction p generalizing q with
  | nil =>
      calc
        eval (padd [] q) t = eval q t := rfl
        _ = 0 + eval q t := by
          rw [Nat.zero_add]
        _ = eval [] t + eval q t := rfl
  | cons a p ih =>
      cases q with
      | nil =>
          calc
            eval (padd (a :: p) []) t = eval (a :: p) t := rfl
            _ = eval (a :: p) t + 0 := by
              rw [Nat.add_zero]
            _ = eval (a :: p) t + eval [] t := rfl
      | cons b q =>
          calc
            eval (padd (a :: p) (b :: q)) t
                = (a + b) + t * eval (padd p q) t := rfl
            _ = (a + b) + t * (eval p t + eval q t) := by
              rw [ih]
            _ = (a + b) + (t * eval p t + t * eval q t) := by
              rw [Nat.mul_add]
            _ = (a + t * eval p t) + (b + t * eval q t) := by
              rw [add_pair_rearrange]
            _ = eval (a :: p) t + eval (b :: q) t := rfl

theorem eval_scaleP (c : Nat) (p : List Nat) (t : Nat) :
    eval (scaleP c p) t = c * eval p t := by
  induction p with
  | nil =>
      calc
        eval (scaleP c []) t = 0 := rfl
        _ = c * 0 := by
          rw [Nat.mul_zero]
        _ = c * eval [] t := rfl
  | cons a p ih =>
      calc
        eval (scaleP c (a :: p)) t = c * a + t * eval (scaleP c p) t := rfl
        _ = c * a + t * (c * eval p t) := by
          rw [ih]
        _ = c * a + (t * c) * eval p t := by
          rw [mul_assoc_pure]
        _ = c * a + (c * t) * eval p t := by
          rw [Nat.mul_comm t c]
        _ = c * a + c * (t * eval p t) := by
          rw [mul_assoc_pure]
        _ = c * (a + t * eval p t) := by
          rw [Nat.mul_add]
        _ = c * eval (a :: p) t := rfl

theorem eval_shiftP (p : List Nat) (t : Nat) :
    eval (shiftP p) t = t * eval p t := by
  calc
    eval (shiftP p) t = 0 + t * eval p t := rfl
    _ = t * eval p t := by
      rw [Nat.zero_add]

theorem eval_addX (c : Nat) (p : List Nat) (t : Nat) :
    eval (addX c p) t = (c + t) * eval p t := by
  calc
    eval (addX c p) t = eval (padd (scaleP c p) (shiftP p)) t := rfl
    _ = eval (scaleP c p) t + eval (shiftP p) t := by
      rw [eval_padd]
    _ = c * eval p t + eval (shiftP p) t := by
      rw [eval_scaleP]
    _ = c * eval p t + t * eval p t := by
      rw [eval_shiftP]
    _ = (c + t) * eval p t := by
      rw [add_mul_pure]

theorem pell_cube_polynomial_recurrence_eval (n : Nat) (t : Nat) :
    eval (Q (n + 2)) t =
      (2 + t) * eval (Q (n + 1)) t + (1 + t) * eval (Q n) t := by
  show
    eval (padd (addX 2 (Q (n + 1))) (addX 1 (Q n))) t =
      (2 + t) * eval (Q (n + 1)) t + (1 + t) * eval (Q n) t
  rw [eval_padd, eval_addX, eval_addX]

theorem total_subcube_recurrence (n : Nat) :
    eval (Q (n + 2)) 1 = 3 * eval (Q (n + 1)) 1 + 2 * eval (Q n) 1 := by
  calc
    eval (Q (n + 2)) 1 =
        (2 + 1) * eval (Q (n + 1)) 1 + (1 + 1) * eval (Q n) 1 := by
      rw [pell_cube_polynomial_recurrence_eval]
    _ = 3 * eval (Q (n + 1)) 1 + 2 * eval (Q n) 1 := rfl

theorem pell_vertex_recurrence (n : Nat) :
    eval (Q (n + 2)) 0 = 2 * eval (Q (n + 1)) 0 + 1 * eval (Q n) 0 := by
  calc
    eval (Q (n + 2)) 0 =
        (2 + 0) * eval (Q (n + 1)) 0 + (1 + 0) * eval (Q n) 0 := by
      rw [pell_cube_polynomial_recurrence_eval]
    _ = 2 * eval (Q (n + 1)) 0 + 1 * eval (Q n) 0 := rfl

theorem total_two : eval (Q 2) 1 = 11 := rfl

theorem total_three : eval (Q 3) 1 = 39 := rfl

end BEDC.Derived.Window6PellCubePolynomial
