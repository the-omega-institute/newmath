namespace BEDC.Derived.Window6LucasDisjointPairTrace

structure Mat3 where
  a11 : Int
  a12 : Int
  a13 : Int
  a21 : Int
  a22 : Int
  a23 : Int
  a31 : Int
  a32 : Int
  a33 : Int
deriving DecidableEq

def mul (X Y : Mat3) : Mat3 :=
  ⟨X.a11 * Y.a11 + X.a12 * Y.a21 + X.a13 * Y.a31,
    X.a11 * Y.a12 + X.a12 * Y.a22 + X.a13 * Y.a32,
    X.a11 * Y.a13 + X.a12 * Y.a23 + X.a13 * Y.a33,
    X.a21 * Y.a11 + X.a22 * Y.a21 + X.a23 * Y.a31,
    X.a21 * Y.a12 + X.a22 * Y.a22 + X.a23 * Y.a32,
    X.a21 * Y.a13 + X.a22 * Y.a23 + X.a23 * Y.a33,
    X.a31 * Y.a11 + X.a32 * Y.a21 + X.a33 * Y.a31,
    X.a31 * Y.a12 + X.a32 * Y.a22 + X.a33 * Y.a32,
    X.a31 * Y.a13 + X.a32 * Y.a23 + X.a33 * Y.a33⟩

def add (X Y : Mat3) : Mat3 :=
  ⟨X.a11 + Y.a11, X.a12 + Y.a12, X.a13 + Y.a13,
    X.a21 + Y.a21, X.a22 + Y.a22, X.a23 + Y.a23,
    X.a31 + Y.a31, X.a32 + Y.a32, X.a33 + Y.a33⟩

def smul (k : Int) (X : Mat3) : Mat3 :=
  ⟨k * X.a11, k * X.a12, k * X.a13,
    k * X.a21, k * X.a22, k * X.a23,
    k * X.a31, k * X.a32, k * X.a33⟩

def I : Mat3 := ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩

def M : Mat3 := ⟨1, 1, 1, 1, 0, 1, 1, 1, 0⟩

def npow (X : Mat3) : Nat → Mat3
  | 0 => I
  | n + 1 => mul (npow X n) X

def trace (X : Mat3) : Int := X.a11 + X.a22 + X.a33

def D (m : Nat) : Int := trace (npow M m)

theorem D_zero : D 0 = 3 := rfl

theorem D_one : D 1 = 1 := rfl

theorem D_two : D 2 = 7 := rfl

theorem D_three : D 3 = 13 := rfl

theorem mat3_eq {X Y : Mat3}
    (h11 : X.a11 = Y.a11) (h12 : X.a12 = Y.a12) (h13 : X.a13 = Y.a13)
    (h21 : X.a21 = Y.a21) (h22 : X.a22 = Y.a22) (h23 : X.a23 = Y.a23)
    (h31 : X.a31 = Y.a31) (h32 : X.a32 = Y.a32) (h33 : X.a33 = Y.a33) :
    X = Y := by
  cases X with
  | mk a11 a12 a13 a21 a22 a23 a31 a32 a33 =>
      cases Y with
      | mk b11 b12 b13 b21 b22 b23 b31 b32 b33 =>
          cases h11
          cases h12
          cases h13
          cases h21
          cases h22
          cases h23
          cases h31
          cases h32
          cases h33
          rfl

private theorem triple_mul_one (a b c : Nat) :
    ((a : Nat) : Int) * (1 : Int) + ((b : Nat) : Int) * (1 : Int) +
      ((c : Nat) : Int) * (1 : Int) = (((a + b + c : Nat)) : Int) := by
  rw [show ((a : Nat) : Int) * (1 : Int) = ((a * 1 : Nat) : Int) by rfl]
  rw [show ((b : Nat) : Int) * (1 : Int) = ((b * 1 : Nat) : Int) by rfl]
  rw [show ((c : Nat) : Int) * (1 : Int) = ((c * 1 : Nat) : Int) by rfl]
  rw [Nat.mul_one, Nat.mul_one, Nat.mul_one]
  rfl

private theorem one_zero_one_mul (a b c : Nat) :
    ((a : Nat) : Int) * (1 : Int) + ((b : Nat) : Int) * (0 : Int) +
      ((c : Nat) : Int) * (1 : Int) = (((a + c : Nat)) : Int) := by
  rw [show ((a : Nat) : Int) * (1 : Int) = ((a * 1 : Nat) : Int) by rfl]
  rw [show ((b : Nat) : Int) * (0 : Int) = ((b * 0 : Nat) : Int) by rfl]
  rw [show ((c : Nat) : Int) * (1 : Int) = ((c * 1 : Nat) : Int) by rfl]
  rw [Nat.mul_one, Nat.mul_zero, Nat.mul_one]
  rfl

private theorem one_one_zero_mul (a b c : Nat) :
    ((a : Nat) : Int) * (1 : Int) + ((b : Nat) : Int) * (1 : Int) +
      ((c : Nat) : Int) * (0 : Int) = (((a + b : Nat)) : Int) := by
  rw [show ((a : Nat) : Int) * (1 : Int) = ((a * 1 : Nat) : Int) by rfl]
  rw [show ((b : Nat) : Int) * (1 : Int) = ((b * 1 : Nat) : Int) by rfl]
  rw [show ((c : Nat) : Int) * (0 : Int) = ((c * 0 : Nat) : Int) by rfl]
  rw [Nat.mul_one, Nat.mul_one, Nat.mul_zero]
  rfl

theorem cayley_hamilton :
    npow M 3 = add (add (npow M 2) (smul 3 (npow M 1))) (npow M 0) := by
  rfl

private theorem nat_add_pair_two (a b c d : Nat) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  calc
    (a + b) + (c + d) = a + (b + (c + d)) := by
      rw [Nat.add_assoc]
    _ = a + ((b + c) + d) := by
      rw [Nat.add_assoc b c d]
    _ = a + ((c + b) + d) := by
      rw [Nat.add_comm b c]
    _ = a + (c + (b + d)) := by
      rw [Nat.add_assoc c b d]
    _ = (a + c) + (b + d) := by
      rw [← Nat.add_assoc]

private theorem nat_add_pair_three (a b c d e f : Nat) :
    (a + b) + (c + d) + (e + f) = (a + c + e) + (b + d + f) := by
  calc
    (a + b) + (c + d) + (e + f) =
        ((a + b) + (c + d)) + (e + f) := rfl
    _ = (a + (b + (c + d))) + (e + f) := by
      rw [Nat.add_assoc a b (c + d)]
    _ = (a + ((b + c) + d)) + (e + f) := by
      rw [Nat.add_assoc b c d]
    _ = (a + ((c + b) + d)) + (e + f) := by
      rw [Nat.add_comm b c]
    _ = (a + (c + (b + d))) + (e + f) := by
      rw [Nat.add_assoc c b d]
    _ = ((a + c) + (b + d)) + (e + f) := by
      rw [← Nat.add_assoc a c (b + d)]
    _ = (a + c) + ((b + d) + (e + f)) := by
      rw [Nat.add_assoc]
    _ = (a + c) + (((b + d) + e) + f) := by
      rw [Nat.add_assoc (b + d) e f]
    _ = (a + c) + ((e + (b + d)) + f) := by
      rw [Nat.add_comm (b + d) e]
    _ = (a + c) + (e + ((b + d) + f)) := by
      rw [Nat.add_assoc e (b + d) f]
    _ = (a + c + e) + ((b + d) + f) := by
      rw [← Nat.add_assoc (a + c) e ((b + d) + f)]
    _ = (a + c + e) + (b + d + f) := rfl

private theorem nat_smul_two (k a b : Nat) :
    k * a + k * b = k * (a + b) := by
  exact (Nat.left_distrib k a b).symm

private theorem nat_smul_three (k a b c : Nat) :
    k * a + k * b + k * c = k * (a + b + c) := by
  rw [Nat.left_distrib k (a + b) c]
  rw [Nat.left_distrib k a b]

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
        _ = (a * c + a) + (b * c + b) :=
          nat_add_pair_two (a * c) (b * c) a b
        _ = a * Nat.succ c + (b * c + b) :=
          congrArg (fun x => x + (b * c + b)) (Nat.mul_succ a c).symm
        _ = a * Nat.succ c + b * Nat.succ c :=
          congrArg (fun x => a * Nat.succ c + x) (Nat.mul_succ b c).symm

structure NMat3 where
  a11 : Nat
  a12 : Nat
  a13 : Nat
  a21 : Nat
  a22 : Nat
  a23 : Nat
  a31 : Nat
  a32 : Nat
  a33 : Nat

private def nmul (X Y : NMat3) : NMat3 :=
  ⟨X.a11 * Y.a11 + X.a12 * Y.a21 + X.a13 * Y.a31,
    X.a11 * Y.a12 + X.a12 * Y.a22 + X.a13 * Y.a32,
    X.a11 * Y.a13 + X.a12 * Y.a23 + X.a13 * Y.a33,
    X.a21 * Y.a11 + X.a22 * Y.a21 + X.a23 * Y.a31,
    X.a21 * Y.a12 + X.a22 * Y.a22 + X.a23 * Y.a32,
    X.a21 * Y.a13 + X.a22 * Y.a23 + X.a23 * Y.a33,
    X.a31 * Y.a11 + X.a32 * Y.a21 + X.a33 * Y.a31,
    X.a31 * Y.a12 + X.a32 * Y.a22 + X.a33 * Y.a32,
    X.a31 * Y.a13 + X.a32 * Y.a23 + X.a33 * Y.a33⟩

private def nadd (X Y : NMat3) : NMat3 :=
  ⟨X.a11 + Y.a11, X.a12 + Y.a12, X.a13 + Y.a13,
    X.a21 + Y.a21, X.a22 + Y.a22, X.a23 + Y.a23,
    X.a31 + Y.a31, X.a32 + Y.a32, X.a33 + Y.a33⟩

private def nsmul (k : Nat) (X : NMat3) : NMat3 :=
  ⟨k * X.a11, k * X.a12, k * X.a13,
    k * X.a21, k * X.a22, k * X.a23,
    k * X.a31, k * X.a32, k * X.a33⟩

private def nI : NMat3 := ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩

private def nM : NMat3 := ⟨1, 1, 1, 1, 0, 1, 1, 1, 0⟩

private def nmulM (X : NMat3) : NMat3 :=
  ⟨X.a11 + X.a12 + X.a13, X.a11 + X.a13, X.a11 + X.a12,
    X.a21 + X.a22 + X.a23, X.a21 + X.a23, X.a21 + X.a22,
    X.a31 + X.a32 + X.a33, X.a31 + X.a33, X.a31 + X.a32⟩

private def nnpow : Nat → NMat3
  | 0 => nI
  | n + 1 => nmulM (nnpow n)

private def ntrace (X : NMat3) : Nat := X.a11 + X.a22 + X.a33

private def ncast (X : NMat3) : Mat3 :=
  ⟨((X.a11 : Nat) : Int), ((X.a12 : Nat) : Int), ((X.a13 : Nat) : Int),
    ((X.a21 : Nat) : Int), ((X.a22 : Nat) : Int), ((X.a23 : Nat) : Int),
    ((X.a31 : Nat) : Int), ((X.a32 : Nat) : Int), ((X.a33 : Nat) : Int)⟩

private theorem nmat3_eq {X Y : NMat3}
    (h11 : X.a11 = Y.a11) (h12 : X.a12 = Y.a12) (h13 : X.a13 = Y.a13)
    (h21 : X.a21 = Y.a21) (h22 : X.a22 = Y.a22) (h23 : X.a23 = Y.a23)
    (h31 : X.a31 = Y.a31) (h32 : X.a32 = Y.a32) (h33 : X.a33 = Y.a33) :
    X = Y := by
  cases X with
  | mk a11 a12 a13 a21 a22 a23 a31 a32 a33 =>
      cases Y with
      | mk b11 b12 b13 b21 b22 b23 b31 b32 b33 =>
          cases h11
          cases h12
          cases h13
          cases h21
          cases h22
          cases h23
          cases h31
          cases h32
          cases h33
          rfl

private theorem nmulM_add (A B : NMat3) :
    nmulM (nadd A B) = nadd (nmulM A) (nmulM B) := by
  apply nmat3_eq
  · change (A.a11 + B.a11) + (A.a12 + B.a12) + (A.a13 + B.a13) =
      (A.a11 + A.a12 + A.a13) + (B.a11 + B.a12 + B.a13)
    exact nat_add_pair_three A.a11 B.a11 A.a12 B.a12 A.a13 B.a13
  · change (A.a11 + B.a11) + (A.a13 + B.a13) =
      (A.a11 + A.a13) + (B.a11 + B.a13)
    exact nat_add_pair_two A.a11 B.a11 A.a13 B.a13
  · change (A.a11 + B.a11) + (A.a12 + B.a12) =
      (A.a11 + A.a12) + (B.a11 + B.a12)
    exact nat_add_pair_two A.a11 B.a11 A.a12 B.a12
  · change (A.a21 + B.a21) + (A.a22 + B.a22) + (A.a23 + B.a23) =
      (A.a21 + A.a22 + A.a23) + (B.a21 + B.a22 + B.a23)
    exact nat_add_pair_three A.a21 B.a21 A.a22 B.a22 A.a23 B.a23
  · change (A.a21 + B.a21) + (A.a23 + B.a23) =
      (A.a21 + A.a23) + (B.a21 + B.a23)
    exact nat_add_pair_two A.a21 B.a21 A.a23 B.a23
  · change (A.a21 + B.a21) + (A.a22 + B.a22) =
      (A.a21 + A.a22) + (B.a21 + B.a22)
    exact nat_add_pair_two A.a21 B.a21 A.a22 B.a22
  · change (A.a31 + B.a31) + (A.a32 + B.a32) + (A.a33 + B.a33) =
      (A.a31 + A.a32 + A.a33) + (B.a31 + B.a32 + B.a33)
    exact nat_add_pair_three A.a31 B.a31 A.a32 B.a32 A.a33 B.a33
  · change (A.a31 + B.a31) + (A.a33 + B.a33) =
      (A.a31 + A.a33) + (B.a31 + B.a33)
    exact nat_add_pair_two A.a31 B.a31 A.a33 B.a33
  · change (A.a31 + B.a31) + (A.a32 + B.a32) =
      (A.a31 + A.a32) + (B.a31 + B.a32)
    exact nat_add_pair_two A.a31 B.a31 A.a32 B.a32

private theorem nmulM_smul (k : Nat) (A : NMat3) :
    nmulM (nsmul k A) = nsmul k (nmulM A) := by
  apply nmat3_eq
  · change k * A.a11 + k * A.a12 + k * A.a13 =
      k * (A.a11 + A.a12 + A.a13)
    exact nat_smul_three k A.a11 A.a12 A.a13
  · change k * A.a11 + k * A.a13 = k * (A.a11 + A.a13)
    exact nat_smul_two k A.a11 A.a13
  · change k * A.a11 + k * A.a12 = k * (A.a11 + A.a12)
    exact nat_smul_two k A.a11 A.a12
  · change k * A.a21 + k * A.a22 + k * A.a23 =
      k * (A.a21 + A.a22 + A.a23)
    exact nat_smul_three k A.a21 A.a22 A.a23
  · change k * A.a21 + k * A.a23 = k * (A.a21 + A.a23)
    exact nat_smul_two k A.a21 A.a23
  · change k * A.a21 + k * A.a22 = k * (A.a21 + A.a22)
    exact nat_smul_two k A.a21 A.a22
  · change k * A.a31 + k * A.a32 + k * A.a33 =
      k * (A.a31 + A.a32 + A.a33)
    exact nat_smul_three k A.a31 A.a32 A.a33
  · change k * A.a31 + k * A.a33 = k * (A.a31 + A.a33)
    exact nat_smul_two k A.a31 A.a33
  · change k * A.a31 + k * A.a32 = k * (A.a31 + A.a32)
    exact nat_smul_two k A.a31 A.a32

private theorem n_cayley_hamilton :
    nnpow 3 = nadd (nadd (nnpow 2) (nsmul 3 (nnpow 1))) (nnpow 0) := by
  rfl

private theorem nM_pow_recurrence (n : Nat) :
    nnpow (n + 3) = nadd (nadd (nnpow (n + 2)) (nsmul 3 (nnpow (n + 1)))) (nnpow n) := by
  induction n with
  | zero =>
      exact n_cayley_hamilton
  | succ n ih =>
      show nnpow (n + 1 + 3) =
        nadd (nadd (nnpow (n + 1 + 2)) (nsmul 3 (nnpow (n + 1 + 1)))) (nnpow (n + 1))
      calc
        nnpow (n + 1 + 3) = nmulM (nnpow (n + 3)) := rfl
        _ = nmulM (nadd (nadd (nnpow (n + 2)) (nsmul 3 (nnpow (n + 1)))) (nnpow n)) :=
          congrArg nmulM ih
        _ = nadd (nmulM (nadd (nnpow (n + 2)) (nsmul 3 (nnpow (n + 1)))))
            (nmulM (nnpow n)) := by
          rw [nmulM_add]
        _ = nadd (nadd (nmulM (nnpow (n + 2))) (nmulM (nsmul 3 (nnpow (n + 1)))))
            (nmulM (nnpow n)) := by
          rw [nmulM_add]
        _ = nadd (nadd (nmulM (nnpow (n + 2))) (nsmul 3 (nmulM (nnpow (n + 1)))))
            (nmulM (nnpow n)) := by
          rw [nmulM_smul]
        _ = nadd (nadd (nnpow (n + 1 + 2)) (nsmul 3 (nnpow (n + 1 + 1)))) (nnpow (n + 1)) := rfl

private theorem ncast_nmulM (A : NMat3) : ncast (nmulM A) = mul (ncast A) M := by
  apply mat3_eq
  · exact (triple_mul_one A.a11 A.a12 A.a13).symm
  · exact (one_zero_one_mul A.a11 A.a12 A.a13).symm
  · exact (one_one_zero_mul A.a11 A.a12 A.a13).symm
  · exact (triple_mul_one A.a21 A.a22 A.a23).symm
  · exact (one_zero_one_mul A.a21 A.a22 A.a23).symm
  · exact (one_one_zero_mul A.a21 A.a22 A.a23).symm
  · exact (triple_mul_one A.a31 A.a32 A.a33).symm
  · exact (one_zero_one_mul A.a31 A.a32 A.a33).symm
  · exact (one_one_zero_mul A.a31 A.a32 A.a33).symm

private theorem M_pow_shape (n : Nat) : npow M n = ncast (nnpow n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [npow, ih]
      exact (ncast_nmulM (nnpow n)).symm

private theorem ncast_nadd (A B : NMat3) :
    ncast (nadd A B) = add (ncast A) (ncast B) := by
  apply mat3_eq <;> rfl

private theorem ncast_nsmul_three (A : NMat3) :
    ncast (nsmul 3 A) = smul 3 (ncast A) := by
  apply mat3_eq <;> rfl

private theorem cast_nM_recurrence (n : Nat) :
    ncast (nnpow (n + 3)) =
      add (add (ncast (nnpow (n + 2))) (smul 3 (ncast (nnpow (n + 1)))))
        (ncast (nnpow n)) := by
  rw [nM_pow_recurrence n, ncast_nadd, ncast_nadd, ncast_nsmul_three]

private theorem ntrace_add (X Y : NMat3) :
    ntrace (nadd X Y) = ntrace X + ntrace Y := by
  exact nat_add_pair_three X.a11 Y.a11 X.a22 Y.a22 X.a33 Y.a33

private theorem ntrace_smul_three (X : NMat3) :
    ntrace (nsmul 3 X) = 3 * ntrace X := by
  exact nat_smul_three 3 X.a11 X.a22 X.a33

private theorem ntrace_recurrence (n : Nat) :
    ntrace (nnpow (n + 3)) =
      ntrace (nnpow (n + 2)) + 3 * ntrace (nnpow (n + 1)) + ntrace (nnpow n) := by
  rw [nM_pow_recurrence n, ntrace_add, ntrace_add, ntrace_smul_three]

private theorem D_shape (n : Nat) : D n = ((ntrace (nnpow n) : Nat) : Int) := by
  unfold D
  rw [M_pow_shape]
  rfl

theorem M_pow_recurrence (n : Nat) :
    npow M (n + 3) =
      add (add (npow M (n + 2)) (smul 3 (npow M (n + 1)))) (npow M n) := by
  rw [M_pow_shape (n + 3), M_pow_shape (n + 2), M_pow_shape (n + 1), M_pow_shape n]
  exact cast_nM_recurrence n

theorem lucas_disjoint_pair_recurrence (n : Nat) :
    D (n + 3) = D (n + 2) + 3 * D (n + 1) + D n := by
  rw [D_shape (n + 3), D_shape (n + 2), D_shape (n + 1), D_shape n]
  rw [ntrace_recurrence]
  rfl

end BEDC.Derived.Window6LucasDisjointPairTrace
