import BEDC.Derived.PrimeUp.UniqueFactorization
import BEDC.Derived.GcdUp
import BEDC.Derived.NatUp
import BEDC.Derived.LucasTheoremBinomUp

namespace BEDC.Derived.PerfectPowerUp

open BEDC.Derived.LucasTheoremBinomUp (NatPrimeUp)

/-
完全幂出口使用有限 prime-row 表。`rows.map FactorRow.prime` 的
`Nodup` 与 `count` 给出有限集边界；`ExponentGcd` 是指数最大公因子证书。
-/

structure FactorRow where
  prime : Nat
  exponent : Nat

abbrev FactorRows := List FactorRow

def NatDvdUp (a b : Nat) : Prop :=
  ∃ q : Nat, b = a * q

def rowValue (row : FactorRow) : Nat :=
  row.prime ^ row.exponent

def factorRowsValue : FactorRows -> Nat
  | [] => 1
  | row :: rows => rowValue row * factorRowsValue rows

def factorRowsPrimes (rows : FactorRows) : List Nat :=
  rows.map FactorRow.prime

def factorRowsPrimeCount (p : Nat) (rows : FactorRows) : Nat :=
  (factorRowsPrimes rows).count p

def FactorRowsValid (rows : FactorRows) : Prop :=
  (factorRowsPrimes rows).Nodup ∧
    ∀ row : FactorRow, row ∈ rows -> NatPrimeUp row.prime ∧ 0 < row.exponent

def FactorRowsOf (n : Nat) (rows : FactorRows) : Prop :=
  FactorRowsValid rows ∧ factorRowsValue rows = n

def allExponentsDvd (k : Nat) (rows : FactorRows) : Prop :=
  ∀ row : FactorRow, row ∈ rows -> NatDvdUp k row.exponent

def CommonExponent (k : Nat) (rows : FactorRows) : Prop :=
  1 < k ∧ allExponentsDvd k rows

def FactorRowsNonempty (rows : FactorRows) : Prop :=
  ∃ row : FactorRow, ∃ tail : FactorRows, rows = row :: tail

def ExponentGcd (rows : FactorRows) (g : Nat) : Prop :=
  0 < g ∧ allExponentsDvd g rows ∧
    ∀ k : Nat, allExponentsDvd k rows -> NatDvdUp k g

def exponentGcd (rows : FactorRows) (g : Nat) : Prop :=
  ExponentGcd rows g

def bestPerfectPowerExponent (rows : FactorRows) (g : Nat) : Prop :=
  ExponentGcd rows g

def IsPerfectPowerByFactorization (n : Nat) (rows : FactorRows) (g : Nat) : Prop :=
  FactorRowsOf n rows ∧ FactorRowsNonempty rows ∧ ExponentGcd rows g ∧ 1 < g

def PerfectPowerWitness (n : Nat) : Prop :=
  ∃ m : Nat, ∃ k : Nat, 1 < k ∧ n = m ^ k

def isPerfectSquareByFactorization (n : Nat) (rows : FactorRows) : Prop :=
  FactorRowsOf n rows ∧ FactorRowsNonempty rows ∧ allExponentsDvd 2 rows

def isPerfectCubeByFactorization (n : Nat) (rows : FactorRows) : Prop :=
  FactorRowsOf n rows ∧ FactorRowsNonempty rows ∧ allExponentsDvd 3 rows

def SmallPerfectPowerValue (n : Nat) : Prop :=
  n = 0 ∨ n = 1

def PerfectPowerDecisionSurface (n : Nat) : Prop :=
  SmallPerfectPowerValue n ∨
    ∃ rows : FactorRows, ∃ g : Nat, IsPerfectPowerByFactorization n rows g

private theorem nat_mul_assoc_pure (a b c : Nat) :
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

private theorem nat_mul_left_comm_pure (a b c : Nat) :
    a * (b * c) = b * (a * c) := by
  calc
    a * (b * c) = (a * b) * c := (nat_mul_assoc_pure a b c).symm
    _ = (b * a) * c := congrArg (fun t => t * c) (Nat.mul_comm a b)
    _ = b * (a * c) := nat_mul_assoc_pure b a c

private theorem natDvdUp_refl (n : Nat) :
    NatDvdUp n n := by
  exact ⟨1, (Nat.mul_one n).symm⟩

private theorem natDvdUp_trans {a b c : Nat} :
    NatDvdUp a b -> NatDvdUp b c -> NatDvdUp a c := by
  intro ab bc
  cases ab with
  | intro q hq =>
      cases bc with
      | intro r hr =>
          exact ⟨q * r, by
            calc
              c = b * r := hr
              _ = (a * q) * r := congrArg (fun x => x * r) hq
              _ = a * (q * r) := nat_mul_assoc_pure a q r⟩

private theorem natDvdUp_large_of_left_large
    {a b : Nat} :
    0 < b -> 1 < a -> NatDvdUp a b -> 1 < b := by
  intro bPos aLarge dvd
  cases dvd with
  | intro q product =>
      cases q with
      | zero =>
          have bZero : b = 0 := by
            calc
              b = a * 0 := product
              _ = 0 := Nat.mul_zero a
          cases bZero
          exact False.elim (Nat.lt_irrefl 0 bPos)
      | succ q =>
          have aLeProduct : a ≤ a * Nat.succ q :=
            Nat.le_mul_of_pos_right a (Nat.succ_pos q)
          have aLeB : a ≤ b := by
            calc
              a ≤ a * Nat.succ q := aLeProduct
              _ = b := product.symm
          exact Nat.lt_of_lt_of_le aLarge aLeB

private theorem one_pow_pure (k : Nat) :
    1 ^ k = 1 := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      calc
        1 ^ Nat.succ k = 1 ^ k * 1 := rfl
        _ = 1 * 1 := congrArg (fun x => x * 1) ih
        _ = 1 := Nat.mul_one 1

private theorem pow_add_pure (a m n : Nat) :
    a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero =>
      calc
        a ^ (m + 0) = a ^ m := rfl
        _ = a ^ m * 1 := (Nat.mul_one (a ^ m)).symm
        _ = a ^ m * a ^ 0 := rfl
  | succ n ih =>
      calc
        a ^ (m + Nat.succ n) = a ^ Nat.succ (m + n) := rfl
        _ = a ^ (m + n) * a := rfl
        _ = (a ^ m * a ^ n) * a := congrArg (fun x => x * a) ih
        _ = a ^ m * (a ^ n * a) := nat_mul_assoc_pure (a ^ m) (a ^ n) a
        _ = a ^ m * a ^ Nat.succ n := rfl

private theorem pow_mul_pure (a m n : Nat) :
    a ^ (m * n) = (a ^ m) ^ n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        a ^ (m * Nat.succ n) = a ^ (m * n + m) := rfl
        _ = a ^ (m * n) * a ^ m := pow_add_pure a (m * n) m
        _ = (a ^ m) ^ n * a ^ m := congrArg (fun x => x * a ^ m) ih
        _ = (a ^ m) ^ Nat.succ n := rfl

private theorem mul_pow_pure (a b k : Nat) :
    (a * b) ^ k = a ^ k * b ^ k := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      calc
        (a * b) ^ Nat.succ k = (a * b) ^ k * (a * b) := rfl
        _ = (a ^ k * b ^ k) * (a * b) := congrArg (fun x => x * (a * b)) ih
        _ = a ^ k * (b ^ k * (a * b)) :=
            nat_mul_assoc_pure (a ^ k) (b ^ k) (a * b)
        _ = a ^ k * (a * (b ^ k * b)) :=
            congrArg (fun x => a ^ k * x) (nat_mul_left_comm_pure (b ^ k) a b)
        _ = (a ^ k * a) * (b ^ k * b) :=
            (nat_mul_assoc_pure (a ^ k) a (b ^ k * b)).symm
        _ = a ^ Nat.succ k * b ^ Nat.succ k := rfl

theorem natDvdUp_refl_public (n : Nat) :
    NatDvdUp n n := by
  exact natDvdUp_refl n

theorem natDvdUp_trans_public {a b c : Nat} :
    NatDvdUp a b -> NatDvdUp b c -> NatDvdUp a c := by
  exact natDvdUp_trans

theorem factorRowsValue_nil :
    factorRowsValue ([] : FactorRows) = 1 := by
  rfl

theorem factorRowsOf_valid {n : Nat} {rows : FactorRows} :
    FactorRowsOf n rows -> FactorRowsValid rows := by
  intro rowsOf
  exact rowsOf.left

theorem factorRowsOf_value {n : Nat} {rows : FactorRows} :
    FactorRowsOf n rows -> factorRowsValue rows = n := by
  intro rowsOf
  exact rowsOf.right

theorem exponentGcd_unfold
    (rows : FactorRows) (g : Nat) :
    exponentGcd rows g = ExponentGcd rows g := by
  rfl

theorem bestPerfectPowerExponent_unfold
    (rows : FactorRows) (g : Nat) :
    bestPerfectPowerExponent rows g = ExponentGcd rows g := by
  rfl

theorem exponentGcd_positive
    {rows : FactorRows} {g : Nat} :
    ExponentGcd rows g -> 0 < g := by
  intro gcdCert
  exact gcdCert.left

theorem exponentGcd_dvd_all
    {rows : FactorRows} {g : Nat} :
    ExponentGcd rows g -> allExponentsDvd g rows := by
  intro gcdCert
  exact gcdCert.right.left

theorem exponentGcd_greatest
    {k g : Nat} {rows : FactorRows} :
    ExponentGcd rows g -> allExponentsDvd k rows -> NatDvdUp k g := by
  intro gcdCert
  exact gcdCert.right.right k

theorem bestPerfectPowerExponent_divides_all
    {rows : FactorRows} {g : Nat} :
    bestPerfectPowerExponent rows g -> allExponentsDvd g rows := by
  intro best
  exact best.right.left

theorem bestPerfectPowerExponent_is_greatest
    {k g : Nat} {rows : FactorRows} :
    bestPerfectPowerExponent rows g -> allExponentsDvd k rows -> NatDvdUp k g := by
  intro best
  exact best.right.right k

theorem commonExponent_iff_gcd_gt_one
    {rows : FactorRows} {g : Nat} :
    ExponentGcd rows g ->
      ((∃ k : Nat, CommonExponent k rows) ↔ 1 < g) := by
  intro gcdCert
  constructor
  · intro witness
    cases witness with
    | intro k common =>
        exact natDvdUp_large_of_left_large gcdCert.left common.left
          (gcdCert.right.right k common.right)
  · intro gcdLarge
    exact ⟨g, ⟨gcdLarge, gcdCert.right.left⟩⟩

theorem perfectPowerCriterion
    {n g : Nat} {rows : FactorRows} :
    FactorRowsOf n rows -> FactorRowsNonempty rows -> ExponentGcd rows g ->
      (IsPerfectPowerByFactorization n rows g ↔
        ∃ k : Nat, CommonExponent k rows) := by
  intro rowsOf nonemptyRows gcdCert
  constructor
  · intro perfect
    exact (commonExponent_iff_gcd_gt_one perfect.right.right.left).mpr
      perfect.right.right.right
  · intro common
    exact ⟨rowsOf, nonemptyRows, gcdCert,
      (commonExponent_iff_gcd_gt_one gcdCert).mp common⟩

theorem factorRowsValue_commonExponent_witness
    (rows : FactorRows) {k : Nat} :
    allExponentsDvd k rows ->
      ∃ m : Nat, factorRowsValue rows = m ^ k := by
  intro dvdRows
  induction rows with
  | nil =>
      exact ⟨1, by
        calc
          factorRowsValue ([] : FactorRows) = 1 := rfl
          _ = 1 ^ k := (one_pow_pure k).symm⟩
  | cons row tail ih =>
      have rowDvd : NatDvdUp k row.exponent :=
        dvdRows row (List.Mem.head tail)
      have tailDvd : allExponentsDvd k tail := by
        intro next mem
        exact dvdRows next (List.Mem.tail row mem)
      cases rowDvd with
      | intro q rowExp =>
          cases ih tailDvd with
          | intro tailRoot tailPower =>
              exact ⟨row.prime ^ q * tailRoot, by
                have rowPower : row.prime ^ row.exponent = (row.prime ^ q) ^ k := by
                  calc
                    row.prime ^ row.exponent = row.prime ^ (k * q) :=
                        congrArg (fun e => row.prime ^ e) rowExp
                    _ = row.prime ^ (q * k) :=
                        congrArg (fun e => row.prime ^ e) (Nat.mul_comm k q)
                    _ = (row.prime ^ q) ^ k := pow_mul_pure row.prime q k
                calc
                  factorRowsValue (row :: tail)
                      = row.prime ^ row.exponent * factorRowsValue tail := rfl
                  _ = row.prime ^ row.exponent * tailRoot ^ k :=
                      congrArg (fun value => row.prime ^ row.exponent * value) tailPower
                  _ = (row.prime ^ q) ^ k * tailRoot ^ k := by
                      exact congrArg (fun value => value * tailRoot ^ k) rowPower
                  _ = (row.prime ^ q * tailRoot) ^ k :=
                      (mul_pow_pure (row.prime ^ q) tailRoot k).symm⟩

theorem factorRowsOf_commonExponent_witness
    {n k : Nat} {rows : FactorRows} :
    FactorRowsOf n rows -> CommonExponent k rows -> PerfectPowerWitness n := by
  intro rowsOf common
  cases factorRowsValue_commonExponent_witness rows common.right with
  | intro root rootPower =>
      exact ⟨root, k, common.left, (factorRowsOf_value rowsOf).symm.trans rootPower⟩

theorem perfectPowerCriterion_witness
    {n g : Nat} {rows : FactorRows} :
    IsPerfectPowerByFactorization n rows g -> PerfectPowerWitness n := by
  intro perfect
  exact factorRowsOf_commonExponent_witness perfect.left
    ⟨perfect.right.right.right, perfect.right.right.left.right.left⟩

theorem squareCriterion
    {n : Nat} {rows : FactorRows} :
    FactorRowsOf n rows -> FactorRowsNonempty rows ->
      (isPerfectSquareByFactorization n rows ↔
        allExponentsDvd 2 rows) := by
  intro rowsOf nonemptyRows
  constructor
  · intro square
    exact square.right.right
  · intro evenExponents
    exact ⟨rowsOf, nonemptyRows, evenExponents⟩

theorem cubeCriterion
    {n : Nat} {rows : FactorRows} :
    FactorRowsOf n rows -> FactorRowsNonempty rows ->
      (isPerfectCubeByFactorization n rows ↔
        allExponentsDvd 3 rows) := by
  intro rowsOf nonemptyRows
  constructor
  · intro cube
    exact cube.right.right
  · intro tripleExponents
    exact ⟨rowsOf, nonemptyRows, tripleExponents⟩

theorem square_is_perfectPower
    {n g : Nat} {rows : FactorRows} :
    ExponentGcd rows g ->
      isPerfectSquareByFactorization n rows ->
        IsPerfectPowerByFactorization n rows g := by
  intro gcdCert square
  have common : ∃ k : Nat, CommonExponent k rows :=
    ⟨2, ⟨by decide, square.right.right⟩⟩
  exact ⟨square.left, square.right.left, gcdCert,
    (commonExponent_iff_gcd_gt_one gcdCert).mp common⟩

theorem cube_is_perfectPower
    {n g : Nat} {rows : FactorRows} :
    ExponentGcd rows g ->
      isPerfectCubeByFactorization n rows ->
        IsPerfectPowerByFactorization n rows g := by
  intro gcdCert cube
  have common : ∃ k : Nat, CommonExponent k rows :=
    ⟨3, ⟨by decide, cube.right.right⟩⟩
  exact ⟨cube.left, cube.right.left, gcdCert,
    (commonExponent_iff_gcd_gt_one gcdCert).mp common⟩

theorem one_smallPerfectPower :
    PerfectPowerDecisionSurface 1 := by
  exact Or.inl (Or.inr rfl)

theorem one_perfectPowerWitness :
    PerfectPowerWitness 1 := by
  exact ⟨1, 2, by decide, by decide⟩

theorem zero_smallPerfectPower :
    PerfectPowerDecisionSurface 0 := by
  exact Or.inl (Or.inl rfl)

theorem zero_perfectPowerWitness :
    PerfectPowerWitness 0 := by
  exact ⟨0, 2, by decide, by decide⟩

theorem factorRowsOf_nonempty_value_gcd_surface
    {n g : Nat} {row : FactorRow} {rows : FactorRows} :
    FactorRowsOf n (row :: rows) ->
      ExponentGcd (row :: rows) g ->
        1 < g -> PerfectPowerDecisionSurface n := by
  intro rowsOf gcdCert gcdLarge
  exact Or.inr ⟨row :: rows, g, rowsOf, ⟨row, rows, rfl⟩, gcdCert, gcdLarge⟩

theorem empty_factorRows_not_perfectPower
    {g : Nat} :
    IsPerfectPowerByFactorization 1 ([] : FactorRows) g -> False := by
  intro perfect
  cases perfect.right.left with
  | intro row rowData =>
      cases rowData with
      | intro tail rowsEq =>
          cases rowsEq

theorem factorRowsValue_single
    (p e : Nat) :
    factorRowsValue [{ prime := p, exponent := e }] = p ^ e := by
  calc
    factorRowsValue [{ prime := p, exponent := e }]
        = p ^ e * factorRowsValue ([] : FactorRows) := rfl
    _ = p ^ e * 1 := rfl
    _ = p ^ e := Nat.mul_one (p ^ e)

theorem single_prime_square_gcd
    (p : Nat) :
    ExponentGcd [{ prime := p, exponent := 2 }] 2 := by
  constructor
  · decide
  · constructor
    · intro row member
      cases member with
      | head =>
          exact natDvdUp_refl 2
      | tail _ tailMember =>
          cases tailMember
    · intro k dvdRows
      exact dvdRows { prime := p, exponent := 2 } (List.Mem.head [])

theorem single_prime_cube_gcd
    (p : Nat) :
    ExponentGcd [{ prime := p, exponent := 3 }] 3 := by
  constructor
  · decide
  · constructor
    · intro row member
      cases member with
      | head =>
          exact natDvdUp_refl 3
      | tail _ tailMember =>
          cases tailMember
    · intro k dvdRows
      exact dvdRows { prime := p, exponent := 3 } (List.Mem.head [])

theorem single_prime_square_surface
    {p : Nat} (prime : NatPrimeUp p) :
    isPerfectSquareByFactorization (p ^ 2)
      [{ prime := p, exponent := 2 }] := by
  let row : FactorRow := { prime := p, exponent := 2 }
  constructor
  · constructor
    · constructor
      · change List.Pairwise (fun x y : Nat => x ≠ y) [p]
        exact List.Pairwise.cons (fun q mem => False.elim (List.not_mem_nil mem))
          List.Pairwise.nil
      · intro row' member
        cases member with
        | head =>
            change NatPrimeUp p ∧ 0 < 2
            exact ⟨prime, by decide⟩
        | tail _ tailMember =>
            cases tailMember
    · exact factorRowsValue_single p 2
  · constructor
    · exact ⟨row, [], rfl⟩
    · intro row' member
      cases member with
      | head =>
          change NatDvdUp 2 2
          exact natDvdUp_refl 2
      | tail _ tailMember =>
          cases tailMember

theorem single_prime_cube_surface
    {p : Nat} (prime : NatPrimeUp p) :
    isPerfectCubeByFactorization (p ^ 3)
      [{ prime := p, exponent := 3 }] := by
  let row : FactorRow := { prime := p, exponent := 3 }
  constructor
  · constructor
    · constructor
      · change List.Pairwise (fun x y : Nat => x ≠ y) [p]
        exact List.Pairwise.cons (fun q mem => False.elim (List.not_mem_nil mem))
          List.Pairwise.nil
      · intro row' member
        cases member with
        | head =>
            change NatPrimeUp p ∧ 0 < 3
            exact ⟨prime, by decide⟩
        | tail _ tailMember =>
            cases tailMember
    · exact factorRowsValue_single p 3
  · constructor
    · exact ⟨row, [], rfl⟩
    · intro row' member
      cases member with
      | head =>
          change NatDvdUp 3 3
          exact natDvdUp_refl 3
      | tail _ tailMember =>
          cases tailMember

theorem single_prime_square_decision_surface
    {p : Nat} (prime : NatPrimeUp p) :
    PerfectPowerDecisionSurface (p ^ 2) := by
  exact Or.inr ⟨[{ prime := p, exponent := 2 }], 2,
    square_is_perfectPower (single_prime_square_gcd p)
      (single_prime_square_surface prime)⟩

theorem single_prime_cube_decision_surface
    {p : Nat} (prime : NatPrimeUp p) :
    PerfectPowerDecisionSurface (p ^ 3) := by
  exact Or.inr ⟨[{ prime := p, exponent := 3 }], 3,
    cube_is_perfectPower (single_prime_cube_gcd p)
      (single_prime_cube_surface prime)⟩

end BEDC.Derived.PerfectPowerUp
