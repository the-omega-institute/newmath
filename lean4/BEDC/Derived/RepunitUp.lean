import BEDC.Derived.GcdUp
import BEDC.Derived.IntUp.Arithmetic

namespace BEDC.Derived.RepunitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp
open BEDC.Derived.PrimeUp

def repunitNat : Nat -> Nat
  | 0 => 0
  | n + 1 => 10 * repunitNat n + 1

def repunitDigits : Nat -> List Nat
  | 0 => []
  | n + 1 => 1 :: repunitDigits n

def digitEval (base : Nat) : List Nat -> Nat
  | [] => 0
  | digit :: tail => digit + base * digitEval base tail

def RepunitDividesIndex (m n : Nat) : Prop :=
  m ∣ n

def repunit : Nat -> BHist :=
  fun n => natToUnary (repunitNat n)

theorem repunitNat_succ (n : Nat) :
    repunitNat (n + 1) = 10 * repunitNat n + 1 := by
  rfl

theorem repunitDigits_length (n : Nat) :
    (repunitDigits n).length = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change Nat.succ ((repunitDigits n).length) = Nat.succ n
      exact congrArg Nat.succ ih

theorem repunitDigits_value_10 (n : Nat) :
    digitEval 10 (repunitDigits n) = repunitNat n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change 1 + 10 * digitEval 10 (repunitDigits n) =
        10 * repunitNat n + 1
      rw [ih]
      exact Nat.add_comm 1 (10 * repunitNat n)

theorem repunit_unary (n : Nat) :
    UnaryHistory (repunit n) := by
  unfold repunit
  exact natToUnary_unary (repunitNat n)

private theorem repunitNat_pos_of_succ (n : Nat) :
    0 < repunitNat (n + 1) := by
  unfold repunitNat
  exact Nat.succ_pos (10 * repunitNat n)

private theorem pow10_pos (n : Nat) :
    0 < 10 ^ n := by
  exact Nat.pow_pos (Nat.succ_pos 9)

private theorem nat_mul_right_zero (a : Nat) :
    a * 0 = 0 := by
  induction a with
  | zero =>
      rfl
  | succ a ih =>
      change a * 0 + 0 = 0
      exact ih

private theorem nat_add_right_zero (a : Nat) :
    a + 0 = a := by
  induction a with
  | zero =>
      rfl
  | succ a ih =>
      exact congrArg Nat.succ ih

private theorem nat_add_right_cancel_clean {a b c : Nat} :
    a + c = b + c -> a = b := by
  induction c generalizing a b with
  | zero =>
      intro h
      rw [nat_add_right_zero] at h
      rw [nat_add_right_zero] at h
      exact h
  | succ c ih =>
      intro h
      rw [Nat.add_succ] at h
      rw [Nat.add_succ] at h
      exact ih (Nat.succ.inj h)

private theorem nat_add_left_cancel_clean {a b c : Nat} :
    a + b = a + c -> b = c := by
  intro h
  exact nat_add_right_cancel_clean (a := b) (b := c) (c := a)
    (by
      rw [Nat.add_comm b a, Nat.add_comm c a]
      exact h)

private theorem nat_mul_right_one (a : Nat) :
    a * 1 = a := by
  change a * Nat.succ 0 = a
  rw [Nat.mul_succ]
  rw [nat_mul_right_zero]
  exact Nat.zero_add a

private theorem nat_mul_assoc_clean (a b c : Nat) :
    (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      rw [nat_mul_right_zero, nat_mul_right_zero, nat_mul_right_zero]
  | succ c ih =>
      calc
        (a * b) * Nat.succ c = (a * b) * c + a * b := Nat.mul_succ (a * b) c
        _ = a * (b * c) + a * b := congrArg (fun x => x + a * b) ih
        _ = a * (b * c + b) := (Nat.mul_add a (b * c) b).symm
        _ = a * (b * Nat.succ c) := by
          rw [Nat.mul_succ]

private theorem nat_mul_left_comm_clean (a b c : Nat) :
    a * (b * c) = b * (a * c) := by
  rw [← nat_mul_assoc_clean a b c]
  rw [Nat.mul_comm a b]
  rw [nat_mul_assoc_clean b a c]

private theorem nat_mul_right_pos_of_pos {a b : Nat} :
    0 < a -> 0 < a * Nat.succ b := by
  intro aPos
  rw [Nat.mul_succ]
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (Nat.lt_add_of_pos_right aPos)

private theorem nat_mul_right_ge_self (a b : Nat) :
    a ≤ a * Nat.succ b := by
  cases b with
  | zero =>
      rw [nat_mul_right_one]
      exact Nat.le.intro (nat_add_right_zero a)
  | succ b =>
      rw [Nat.mul_succ]
      rw [Nat.add_comm]
      exact Nat.le_add_right a (a * Nat.succ b)

private theorem nat_mul_right_lt_of_lt {a b c : Nat} :
    a < b -> 0 < c -> a < b * c := by
  intro aLtB cPos
  cases c with
  | zero =>
      exact False.elim (Nat.not_lt_zero _ cPos)
  | succ c =>
      exact Nat.lt_of_lt_of_le aLtB (nat_mul_right_ge_self b c)

private theorem nat_mul_left_lt_of_lt_pos {a b c : Nat} :
    0 < a -> b < c -> a * b < a * c := by
  intro aPos bLtC
  have succLe : Nat.succ b ≤ c := Nat.succ_le_of_lt bLtC
  cases Nat.le.dest succLe with
  | intro t ht =>
      have cEq : c = Nat.succ b + t := ht.symm
      subst c
      rw [Nat.mul_add]
      exact Nat.lt_of_lt_of_le
        (by
          calc
            a * b < a * b + a := Nat.lt_add_of_pos_right aPos
            _ = a * Nat.succ b := (Nat.mul_succ a b).symm)
        (Nat.le_add_right (a * Nat.succ b) (a * t))

private theorem repunitNat_mul_block (a b : Nat) :
    repunitNat (a + b) = 10 ^ b * repunitNat a + repunitNat b := by
  induction b with
  | zero =>
      rw [nat_add_right_zero]
      change repunitNat a = 1 * repunitNat a + 0
      rw [Nat.one_mul, nat_add_right_zero]
  | succ b ih =>
      calc
        repunitNat (a + Nat.succ b)
            = 10 * repunitNat (a + b) + 1 := by
                rw [Nat.add_succ]
                rfl
        _ = 10 * (10 ^ b * repunitNat a + repunitNat b) + 1 := by
                rw [ih]
        _ = 10 * (10 ^ b * repunitNat a) + 10 * repunitNat b + 1 := by
                rw [Nat.mul_add]
        _ = (10 * 10 ^ b) * repunitNat a + (10 * repunitNat b + 1) := by
                rw [nat_mul_assoc_clean]
                rw [Nat.add_assoc]
        _ = 10 ^ Nat.succ b * repunitNat a + repunitNat (Nat.succ b) := by
                rw [repunitNat_succ b]
                rw [Nat.pow_succ]
                rw [Nat.mul_comm (10 ^ b) 10]

theorem repunitNat_add (a b : Nat) :
    repunitNat (a + b) = 10 ^ b * repunitNat a + repunitNat b :=
  repunitNat_mul_block a b

theorem repunitNat_dvd_of_dvd_index {m n : Nat} :
    m ∣ n -> repunitNat m ∣ repunitNat n := by
  intro divides
  cases divides with
  | intro q hq =>
      subst n
      induction q with
      | zero =>
          exact ⟨0, rfl⟩
      | succ q ih =>
          cases ih with
          | intro w hw =>
              have block :
                  repunitNat (m * Nat.succ q) =
                    10 ^ m * repunitNat (m * q) + repunitNat m := by
                have sumEq : m * Nat.succ q = m * q + m := Nat.mul_succ m q
                rw [sumEq]
                exact repunitNat_mul_block (m * q) m
              exact ⟨10 ^ m * w + 1, by
                rw [block, hw]
                calc
                  10 ^ m * (repunitNat m * w) + repunitNat m
                      = repunitNat m * (10 ^ m * w) + repunitNat m := by
                          rw [nat_mul_left_comm_clean]
                  _ = repunitNat m * (10 ^ m * w) + repunitNat m * 1 := by
                          rw [nat_mul_right_one]
                  _ = repunitNat m * (10 ^ m * w + 1) := by
                          exact (Nat.mul_add (repunitNat m) (10 ^ m * w) 1).symm⟩

private theorem repunitNat_lt_of_lt_index {r m : Nat} :
    r < m -> repunitNat r < repunitNat m := by
  intro h
  have succLe : Nat.succ r ≤ m := Nat.succ_le_of_lt h
  cases Nat.le.dest succLe with
  | intro t ht =>
      have mEq : m = r + Nat.succ t := by
        exact ht.symm.trans (by rw [Nat.succ_add, Nat.add_succ])
      subst m
      rw [mEq]
      rw [repunitNat_mul_block r (Nat.succ t)]
      have positiveTail : 0 < repunitNat (Nat.succ t) := repunitNat_pos_of_succ t
      have leftNonneg : repunitNat r ≤ 10 ^ Nat.succ t * repunitNat r := by
        cases repunitNat r with
        | zero =>
            exact Nat.zero_le _
        | succ w =>
            have powPositive := pow10_pos (Nat.succ t)
            have oneLePow : 1 ≤ 10 ^ Nat.succ t := Nat.succ_le_of_lt powPositive
            calc
              w + 1 = 1 * (w + 1) := (Nat.one_mul (w + 1)).symm
              _ ≤ 10 ^ Nat.succ t * (w + 1) :=
                Nat.mul_le_mul_right (w + 1) oneLePow
      exact Nat.lt_of_le_of_lt leftNonneg
        (Nat.lt_add_of_pos_right positiveTail)

private theorem repunitNat_pos_index_of_pos {n : Nat} :
    0 < n -> 0 < repunitNat n := by
  intro nPos
  cases n with
  | zero =>
      exact False.elim (Nat.not_lt_zero _ nPos)
  | succ n =>
      exact repunitNat_pos_of_succ n

private theorem repunitNat_eq_zero_index_zero {n : Nat} :
    repunitNat n = 0 -> n = 0 := by
  intro repZero
  cases n with
  | zero =>
      rfl
  | succ n =>
      have positive : 0 < repunitNat (Nat.succ n) := repunitNat_pos_of_succ n
      rw [repZero] at positive
      exact False.elim (Nat.not_lt_zero _ positive)

private theorem nat_dvd_zero_clean (a : Nat) :
    a ∣ 0 := by
  exact ⟨0, by rw [nat_mul_right_zero]⟩

private theorem nat_dvd_refl_clean (a : Nat) :
    a ∣ a := by
  exact ⟨1, by rw [nat_mul_right_one]⟩

private theorem repunitNat_small_divisor_absurd {r m q : Nat} :
    0 < r -> r < m -> repunitNat r = repunitNat m * q -> False := by
  intro rPos rLtM h
  have rLtRep : repunitNat r < repunitNat m := repunitNat_lt_of_lt_index rLtM
  have mPos : 0 < repunitNat m :=
    repunitNat_pos_index_of_pos (Nat.lt_of_le_of_lt (Nat.zero_le r) rLtM)
  cases q with
  | zero =>
      rw [nat_mul_right_zero] at h
      have rRepPos : 0 < repunitNat r := repunitNat_pos_index_of_pos rPos
      rw [h] at rRepPos
      exact False.elim (Nat.not_lt_zero _ rRepPos)
  | succ q =>
      have leSelf : repunitNat m ≤ repunitNat m * Nat.succ q :=
        nat_mul_right_ge_self (repunitNat m) q
      rw [← h] at leSelf
      exact Nat.lt_irrefl _
        (Nat.lt_of_lt_of_le rLtRep leSelf)

private theorem nat_eq_or_lt_of_le_succ {a b : Nat} :
    a ≤ Nat.succ b -> a = Nat.succ b ∨ a < Nat.succ b := by
  intro h
  cases Nat.lt_or_ge a (Nat.succ b) with
  | inl hlt =>
      exact Or.inr hlt
  | inr hge =>
      have eq : a = Nat.succ b :=
        Nat.le_antisymm h hge
      exact Or.inl eq

private theorem nat_decompose_ge (a b : Nat) :
    b ≤ a -> ∃ t : Nat, a = b + t := by
  intro h
  cases Nat.le.dest h with
  | intro t ht =>
      exact ⟨t, ht.symm⟩

private theorem nat_pow10_le_of_lt {q k : Nat} :
    ¬ q < 10 ^ k -> 10 ^ k ≤ q := by
  intro h
  exact Nat.ge_of_not_lt h

private theorem nat_quotient_large_or_small (q k : Nat) :
    q < 10 ^ k ∨ ∃ w : Nat, q = 10 ^ k + w := by
  cases Nat.lt_or_ge q (10 ^ k) with
  | inl small =>
      exact Or.inl small
  | inr large =>
      exact Or.inr (nat_decompose_ge q (10 ^ k) large)

private theorem nat_mul_add_factor (a b c : Nat) :
    a * (b + c) = a * b + a * c := by
  induction c with
  | zero =>
      rw [nat_add_right_zero, nat_mul_right_zero, nat_add_right_zero]
  | succ c ih =>
      rw [Nat.add_succ, Nat.mul_succ, ih, Nat.mul_succ]
      rw [Nat.add_assoc]

private theorem repunitNat_dvd_step_down_eq {m k q : Nat} :
    0 < m ->
      repunitNat (m + k) = repunitNat m * q ->
        repunitNat m ∣ repunitNat k := by
  intro mPos hq
  have block := repunitNat_mul_block m k
  rw [block] at hq
  have divisorPos : 0 < repunitNat m := repunitNat_pos_index_of_pos mPos
  cases nat_quotient_large_or_small q k with
  | inl small =>
      have rightLt :
          repunitNat m * q < repunitNat m * 10 ^ k :=
        nat_mul_left_lt_of_lt_pos divisorPos small
      have leftLe :
          repunitNat m * 10 ^ k ≤ 10 ^ k * repunitNat m + repunitNat k := by
        rw [Nat.mul_comm (repunitNat m) (10 ^ k)]
        exact Nat.le_add_right _ _
      rw [← hq] at rightLt
      exact False.elim
        (Nat.lt_irrefl _
          (Nat.lt_of_lt_of_le rightLt leftLe))
  | inr large =>
      cases large with
      | intro w qEq =>
          have factorEq :
              repunitNat m * q =
                10 ^ k * repunitNat m + repunitNat m * w := by
            rw [qEq]
            rw [nat_mul_add_factor]
            rw [Nat.mul_comm (repunitNat m) (10 ^ k)]
          have eqTail :
              10 ^ k * repunitNat m + repunitNat k =
                10 ^ k * repunitNat m + repunitNat m * w := by
            exact hq.trans factorEq
          have tailEq :
              repunitNat k = repunitNat m * w :=
            nat_add_left_cancel_clean eqTail
          exact ⟨w, tailEq⟩

private theorem repunitNat_dvd_step_down {m k : Nat} :
    0 < m ->
      repunitNat m ∣ repunitNat (m + k) ->
        repunitNat m ∣ repunitNat k := by
  intro mPos divides
  cases divides with
  | intro q hq =>
      exact repunitNat_dvd_step_down_eq mPos hq

private theorem repunitNat_dvd_index_of_dvd_pos {m n : Nat} :
    0 < m -> repunitNat m ∣ repunitNat n -> m ∣ n := by
  intro mPos divides
  induction n using Nat.strongRecOn with
  | ind n ih =>
      cases Nat.lt_or_ge n m with
      | inl nLtM =>
          cases n with
          | zero =>
              exact nat_dvd_zero_clean m
          | succ n =>
              cases divides with
              | intro q hq =>
                  have nPos : 0 < Nat.succ n := Nat.succ_pos n
                  have divisorPos : 0 < repunitNat (Nat.succ n) :=
                    repunitNat_pos_index_of_pos nPos
                  cases q with
                  | zero =>
                      rw [nat_mul_right_zero] at hq
                      rw [hq] at divisorPos
                      exact False.elim (Nat.not_lt_zero _ divisorPos)
                  | succ q =>
                      exact False.elim
                        (repunitNat_small_divisor_absurd nPos nLtM hq)
      | inr mLeN =>
          cases Nat.le.dest mLeN with
          | intro k hk =>
              have nEq : n = m + k := hk.symm
              subst n
              cases k with
              | zero =>
                  rw [nat_add_right_zero]
                  exact nat_dvd_refl_clean m
              | succ k =>
                  have kLt : Nat.succ k < m + Nat.succ k := by
                    exact Nat.lt_add_of_pos_left mPos
                  have tailDivides :
                      repunitNat m ∣ repunitNat (Nat.succ k) :=
                    repunitNat_dvd_step_down mPos divides
                  cases ih (Nat.succ k) kLt tailDivides with
                  | intro q hq =>
                      exact ⟨Nat.succ q, by
                        calc
                          m + Nat.succ k = Nat.succ k + m := Nat.add_comm m (Nat.succ k)
                          _ = m * q + m := by rw [hq]
                          _ = m * Nat.succ q := (Nat.mul_succ m q).symm⟩

theorem repunitNat_dvd_index_of_dvd {m n : Nat} :
    repunitNat m ∣ repunitNat n -> m ∣ n := by
  intro divides
  cases Nat.decEq m 0 with
  | isTrue mZero =>
      subst m
      cases divides with
      | intro q hq =>
      have repZero : repunitNat n = 0 := by
        change repunitNat n = 0 * q at hq
        rw [Nat.zero_mul] at hq
        exact hq
      have nZero : n = 0 := by
        cases n with
        | zero =>
            rfl
        | succ r =>
            have positive : 0 < repunitNat (Nat.succ r) :=
              repunitNat_pos_of_succ r
            rw [repZero] at positive
            exact False.elim (Nat.not_lt_zero _ positive)
      subst n
      exact ⟨0, rfl⟩
  | isFalse mNonzero =>
      have mPos : 0 < m := Nat.pos_of_ne_zero mNonzero
      exact repunitNat_dvd_index_of_dvd_pos mPos divides

theorem repunitNat_dvd_iff {m n : Nat} :
    repunitNat m ∣ repunitNat n ↔ m ∣ n := by
  constructor
  · exact repunitNat_dvd_index_of_dvd
  · exact repunitNat_dvd_of_dvd_index

private theorem natToUnary_mul_rel (a b : Nat) :
    NatMul (natToUnary a) (natToUnary b) (natToUnary (a * b)) := by
  have total := NatMul_total (natToUnary_unary a) (natToUnary_unary b)
  cases total with
  | intro result resultData =>
      have sameResult : hsame result (natToUnary (a * b)) :=
        (BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.right.right.left
          resultData.left (natToUnary_unary _)).mpr (by
            rw [NatMul_bwordLength resultData.right]
            rw [natToUnary_length, natToUnary_length, natToUnary_length])
      exact (NatMul_result_hsame_transport resultData.right sameResult).right

theorem repunit_dvd_of_index_dvd {m n : Nat} :
    m ∣ n -> NatDivides (repunit m) (repunit n) := by
  intro divides
  cases repunitNat_dvd_of_dvd_index divides with
  | intro q hq =>
      unfold repunit
      exact ⟨natToUnary q, natToUnary_unary q, by
        have rel := natToUnary_mul_rel (repunitNat m) q
        rw [← hq] at rel
        exact rel⟩

theorem index_dvd_of_repunit_dvd {m n : Nat} :
    NatDivides (repunit m) (repunit n) -> m ∣ n := by
  intro divides
  have lengthDivides : repunitNat m ∣ repunitNat n := by
    cases divides with
    | intro q qData =>
        exact ⟨bwordLength q, by
          unfold repunit at qData
          rw [← natToUnary_length (repunitNat n)]
          rw [NatMul_bwordLength qData.right]
          rw [natToUnary_length (repunitNat m)]⟩
  exact repunitNat_dvd_index_of_dvd lengthDivides

theorem repunit_dvd_iff {m n : Nat} :
    NatDivides (repunit m) (repunit n) ↔ m ∣ n := by
  constructor
  · exact index_dvd_of_repunit_dvd
  · exact repunit_dvd_of_index_dvd

end BEDC.Derived.RepunitUp
