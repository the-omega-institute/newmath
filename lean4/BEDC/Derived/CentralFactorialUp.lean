import BEDC.Derived.StirlingUp
import BEDC.Derived.StirlingFirstUp
import BEDC.Derived.IntUp.CommRing

namespace BEDC.Derived.CentralFactorialUp

abbrev Z : Type := BEDC.Algebra.Rel.IntegerUp
abbrev Zeq : Z -> Z -> Prop := BEDC.Algebra.Rel.IntEq

def integerRing : BEDC.Algebra.Rel.RelCommRing Z Zeq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

def zOfNat (n : Nat) : Z :=
  BEDC.Derived.RationalUp.intOfNat
    (BEDC.Derived.IntUp.natToUnary n)
    (BEDC.Derived.IntUp.natToUnary_unary n)

abbrev zzero : Z := BEDC.Algebra.Rel.intZero
abbrev zone : Z := BEDC.Algebra.Rel.intOne
abbrev zadd : Z -> Z -> Z := BEDC.Algebra.Rel.IntAdd
abbrev zmul : Z -> Z -> Z := BEDC.Algebra.Rel.IntMul
abbrev zneg : Z -> Z := BEDC.Algebra.Rel.IntNeg

def zsub (a b : Z) : Z :=
  integerRing.sub a b

-- 第二类中心阶乘数。递归保持奇偶层, 系数为当前列指标平方。
def centralFactorialSecond : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | 1, 0 => 0
  | 1, 1 => 1
  | 1, Nat.succ (Nat.succ _) => 0
  | Nat.succ (Nat.succ n), 0 =>
      0 * 0 * centralFactorialSecond n 0
  | Nat.succ (Nat.succ n), 1 =>
      1 * 1 * centralFactorialSecond n 1
  | Nat.succ (Nat.succ n), Nat.succ (Nat.succ k) =>
      centralFactorialSecond n k +
        Nat.succ (Nat.succ k) * Nat.succ (Nat.succ k) *
          centralFactorialSecond n (Nat.succ (Nat.succ k))

-- 第一类中心阶乘数为有符号整数; 负号由 `IntegerUp` 的环结构承载。
def centralFactorialFirst : Nat -> Nat -> Z
  | 0, 0 => zone
  | 0, Nat.succ _ => zzero
  | 1, 0 => zzero
  | 1, 1 => zone
  | 1, Nat.succ (Nat.succ _) => zzero
  | Nat.succ (Nat.succ n), 0 =>
      zsub zzero (zmul (zOfNat (n * n)) (centralFactorialFirst n 0))
  | Nat.succ (Nat.succ n), 1 =>
      zsub zzero (zmul (zOfNat (n * n)) (centralFactorialFirst n 1))
  | Nat.succ (Nat.succ n), Nat.succ (Nat.succ k) =>
      zsub (centralFactorialFirst n k)
        (zmul (zOfNat (n * n))
          (centralFactorialFirst n (Nat.succ (Nat.succ k))))

def centralFactorialSecondPrefix (n : Nat) : Nat -> Nat
  | 0 => centralFactorialSecond n 0
  | Nat.succ k =>
      centralFactorialSecondPrefix n k +
        centralFactorialSecond n (Nat.succ k)

def centralFactorialSecondRowSum (n : Nat) : Nat :=
  centralFactorialSecondPrefix n n

theorem centralFactorialSecond_zero_zero :
    centralFactorialSecond 0 0 = 1 := by
  rfl

theorem centralFactorialSecond_zero_succ (k : Nat) :
    centralFactorialSecond 0 (Nat.succ k) = 0 := by
  rfl

theorem centralFactorialSecond_one_zero :
    centralFactorialSecond 1 0 = 0 := by
  rfl

theorem centralFactorialSecond_one_one :
    centralFactorialSecond 1 1 = 1 := by
  rfl

theorem centralFactorialSecond_one_above (k : Nat) :
    centralFactorialSecond 1 (Nat.succ (Nat.succ k)) = 0 := by
  rfl

theorem centralFactorialSecond_recurrence (n k : Nat) :
    centralFactorialSecond (Nat.succ (Nat.succ n)) (Nat.succ (Nat.succ k)) =
      centralFactorialSecond n k +
        Nat.succ (Nat.succ k) * Nat.succ (Nat.succ k) *
          centralFactorialSecond n (Nat.succ (Nat.succ k)) := by
  rfl

theorem centralFactorialSecond_low_zero_recurrence (n : Nat) :
    centralFactorialSecond (Nat.succ (Nat.succ n)) 0 =
      0 * 0 * centralFactorialSecond n 0 := by
  rfl

theorem centralFactorialSecond_low_one_recurrence (n : Nat) :
    centralFactorialSecond (Nat.succ (Nat.succ n)) 1 =
      1 * 1 * centralFactorialSecond n 1 := by
  rfl

theorem centralFactorialFirst_zero_zero :
    Zeq (centralFactorialFirst 0 0) zone := by
  exact integerRing.refl zone

theorem centralFactorialFirst_zero_succ (k : Nat) :
    Zeq (centralFactorialFirst 0 (Nat.succ k)) zzero := by
  exact integerRing.refl zzero

theorem centralFactorialFirst_one_zero :
    Zeq (centralFactorialFirst 1 0) zzero := by
  exact integerRing.refl zzero

theorem centralFactorialFirst_one_one :
    Zeq (centralFactorialFirst 1 1) zone := by
  exact integerRing.refl zone

theorem centralFactorialFirst_one_above (k : Nat) :
    Zeq (centralFactorialFirst 1 (Nat.succ (Nat.succ k))) zzero := by
  exact integerRing.refl zzero

theorem centralFactorialFirst_recurrence (n k : Nat) :
    Zeq
      (centralFactorialFirst (Nat.succ (Nat.succ n)) (Nat.succ (Nat.succ k)))
      (zsub (centralFactorialFirst n k)
        (zmul (zOfNat (n * n))
          (centralFactorialFirst n (Nat.succ (Nat.succ k))))) := by
  exact integerRing.refl _

theorem centralFactorialFirst_low_zero_recurrence (n : Nat) :
    Zeq (centralFactorialFirst (Nat.succ (Nat.succ n)) 0)
      (zsub zzero (zmul (zOfNat (n * n)) (centralFactorialFirst n 0))) := by
  exact integerRing.refl _

theorem centralFactorialFirst_low_one_recurrence (n : Nat) :
    Zeq (centralFactorialFirst (Nat.succ (Nat.succ n)) 1)
      (zsub zzero (zmul (zOfNat (n * n)) (centralFactorialFirst n 1))) := by
  exact integerRing.refl _

theorem centralFactorialSecond_self_and_above :
    ∀ n : Nat, centralFactorialSecond n n = 1 ∧
      ∀ extra : Nat,
        centralFactorialSecond n (Nat.succ (n + extra)) = 0
  | 0 => by
      constructor
      · rfl
      · intro extra
        rfl
  | 1 => by
      constructor
      · rfl
      · intro extra
        cases extra with
        | zero =>
            rfl
        | succ _ =>
            rfl
  | Nat.succ (Nat.succ n) => by
      have ih := centralFactorialSecond_self_and_above n
      constructor
      · change centralFactorialSecond n n +
          Nat.succ (Nat.succ n) * Nat.succ (Nat.succ n) *
            centralFactorialSecond n (Nat.succ (Nat.succ n)) = 1
        have above :
            centralFactorialSecond n (Nat.succ (Nat.succ n)) = 0 := by
          have h := ih.right 1
          rw [Nat.add_one] at h
          exact h
        rw [above, ih.left]
        rfl
      · intro extra
        rw [Nat.succ_add, Nat.succ_add]
        change
          centralFactorialSecond n (Nat.succ (n + extra)) +
            Nat.succ (Nat.succ (Nat.succ (n + extra))) *
              Nat.succ (Nat.succ (Nat.succ (n + extra))) *
                centralFactorialSecond n
                  (Nat.succ (Nat.succ (Nat.succ (n + extra)))) = 0
        have far :
            centralFactorialSecond n
              (Nat.succ (Nat.succ (Nat.succ (n + extra)))) = 0 := by
          have h := ih.right (Nat.succ (Nat.succ extra))
          rw [Nat.add_succ, Nat.add_succ] at h
          exact h
        rw [ih.right extra, far]
        rfl

theorem centralFactorialSecond_self (n : Nat) :
    centralFactorialSecond n n = 1 :=
  (centralFactorialSecond_self_and_above n).left

theorem centralFactorialSecond_above (n extra : Nat) :
    centralFactorialSecond n (Nat.succ (n + extra)) = 0 :=
  (centralFactorialSecond_self_and_above n).right extra

theorem centralFactorialSecond_self_matches_stirlingSecond_self (n : Nat) :
    centralFactorialSecond n n =
      BEDC.Derived.StirlingUp.stirlingSecond n n := by
  rw [centralFactorialSecond_self,
    BEDC.Derived.StirlingUp.stirlingSecond_self]

theorem centralFactorialSecond_above_matches_stirlingSecond_above
    (n extra : Nat) :
    centralFactorialSecond n (Nat.succ (n + extra)) =
      BEDC.Derived.StirlingUp.stirlingSecond n
        (Nat.succ (n + extra)) := by
  rw [centralFactorialSecond_above,
    BEDC.Derived.StirlingUp.stirlingSecond_above]

theorem centralFactorialSecond_stirling_relation (n extra : Nat) :
    centralFactorialSecond n n =
        BEDC.Derived.StirlingUp.stirlingSecond n n ∧
      centralFactorialSecond n (Nat.succ (n + extra)) =
        BEDC.Derived.StirlingUp.stirlingSecond n
          (Nat.succ (n + extra)) := by
  exact And.intro
    (centralFactorialSecond_self_matches_stirlingSecond_self n)
    (centralFactorialSecond_above_matches_stirlingSecond_above n extra)

theorem centralFactorialSecond_zero_row_stirling (k : Nat) :
    centralFactorialSecond 0 k =
      BEDC.Derived.StirlingUp.stirlingSecond 0 k := by
  cases k with
  | zero =>
      rfl
  | succ _ =>
      rfl

theorem centralFactorialSecond_one_row_stirling (k : Nat) :
    centralFactorialSecond 1 k =
      BEDC.Derived.StirlingUp.stirlingSecond 1 k := by
  cases k with
  | zero =>
      rfl
  | succ k =>
      cases k with
      | zero =>
          rfl
      | succ _ =>
          rfl

theorem centralFactorialFirst_zero_row_stirling (k : Nat) :
    Zeq (centralFactorialFirst 0 k)
      (zOfNat (BEDC.Derived.StirlingFirstUp.stirlingFirst 0 k)) := by
  cases k with
  | zero =>
      exact integerRing.refl _
  | succ _ =>
      exact integerRing.refl _

theorem centralFactorialFirst_one_row_stirling (k : Nat) :
    Zeq (centralFactorialFirst 1 k)
      (zOfNat (BEDC.Derived.StirlingFirstUp.stirlingFirst 1 k)) := by
  cases k with
  | zero =>
      exact integerRing.refl _
  | succ k =>
      cases k with
      | zero =>
          exact integerRing.refl _
      | succ _ =>
          exact integerRing.refl _

theorem centralFactorial_seed_rows_match_stirling (k : Nat) :
    centralFactorialSecond 0 k =
        BEDC.Derived.StirlingUp.stirlingSecond 0 k ∧
      centralFactorialSecond 1 k =
        BEDC.Derived.StirlingUp.stirlingSecond 1 k ∧
      Zeq (centralFactorialFirst 0 k)
        (zOfNat (BEDC.Derived.StirlingFirstUp.stirlingFirst 0 k)) ∧
      Zeq (centralFactorialFirst 1 k)
        (zOfNat (BEDC.Derived.StirlingFirstUp.stirlingFirst 1 k)) := by
  exact And.intro (centralFactorialSecond_zero_row_stirling k)
    (And.intro (centralFactorialSecond_one_row_stirling k)
      (And.intro (centralFactorialFirst_zero_row_stirling k)
        (centralFactorialFirst_one_row_stirling k)))

theorem centralFactorialFirst_stirling_relation (k : Nat) :
    Zeq (centralFactorialFirst 0 k)
        (zOfNat (BEDC.Derived.StirlingFirstUp.stirlingFirst 0 k)) ∧
      Zeq (centralFactorialFirst 1 k)
        (zOfNat (BEDC.Derived.StirlingFirstUp.stirlingFirst 1 k)) := by
  exact And.intro
    (centralFactorialFirst_zero_row_stirling k)
    (centralFactorialFirst_one_row_stirling k)

theorem centralFactorialSecondPrefix_succ (n k : Nat) :
    centralFactorialSecondPrefix n (Nat.succ k) =
      centralFactorialSecondPrefix n k +
        centralFactorialSecond n (Nat.succ k) := by
  rfl

theorem centralFactorialSecondRowSum_definition (n : Nat) :
    centralFactorialSecondRowSum n =
      centralFactorialSecondPrefix n n := by
  rfl

theorem centralFactorialSecond_2_2 :
    centralFactorialSecond 2 2 = 1 := by
  rfl

theorem centralFactorialSecond_3_1 :
    centralFactorialSecond 3 1 = 1 := by
  rfl

theorem centralFactorialSecond_3_3 :
    centralFactorialSecond 3 3 = 1 := by
  rfl

theorem centralFactorialSecond_4_2 :
    centralFactorialSecond 4 2 = 4 := by
  rfl

theorem centralFactorialSecond_4_4 :
    centralFactorialSecond 4 4 = 1 := by
  rfl

theorem centralFactorialSecond_5_1 :
    centralFactorialSecond 5 1 = 1 := by
  rfl

theorem centralFactorialSecond_5_3 :
    centralFactorialSecond 5 3 = 10 := by
  rfl

theorem centralFactorialSecond_5_5 :
    centralFactorialSecond 5 5 = 1 := by
  rfl

theorem centralFactorialSecondRowSum_zero :
    centralFactorialSecondRowSum 0 = 1 := by
  rfl

theorem centralFactorialSecondRowSum_one :
    centralFactorialSecondRowSum 1 = 1 := by
  rfl

theorem centralFactorialSecondRowSum_two :
    centralFactorialSecondRowSum 2 = 1 := by
  rfl

theorem centralFactorialSecondRowSum_three :
    centralFactorialSecondRowSum 3 = 2 := by
  rfl

theorem centralFactorialSecondRowSum_four :
    centralFactorialSecondRowSum 4 = 5 := by
  rfl

theorem centralFactorialSecondRowSum_five :
    centralFactorialSecondRowSum 5 = 12 := by
  rfl

theorem centralFactorialSecond_small_values :
    centralFactorialSecond 2 2 = 1 ∧
      centralFactorialSecond 3 1 = 1 ∧
      centralFactorialSecond 3 3 = 1 ∧
      centralFactorialSecond 4 2 = 4 ∧
      centralFactorialSecond 4 4 = 1 ∧
      centralFactorialSecond 5 1 = 1 ∧
      centralFactorialSecond 5 3 = 10 ∧
      centralFactorialSecond 5 5 = 1 := by
  exact And.intro centralFactorialSecond_2_2
    (And.intro centralFactorialSecond_3_1
      (And.intro centralFactorialSecond_3_3
        (And.intro centralFactorialSecond_4_2
          (And.intro centralFactorialSecond_4_4
            (And.intro centralFactorialSecond_5_1
              (And.intro centralFactorialSecond_5_3
                centralFactorialSecond_5_5))))))

theorem centralFactorialSecond_row_sum_small_values :
    centralFactorialSecondRowSum 0 = 1 ∧
      centralFactorialSecondRowSum 1 = 1 ∧
      centralFactorialSecondRowSum 2 = 1 ∧
      centralFactorialSecondRowSum 3 = 2 ∧
      centralFactorialSecondRowSum 4 = 5 ∧
      centralFactorialSecondRowSum 5 = 12 := by
  exact And.intro centralFactorialSecondRowSum_zero
    (And.intro centralFactorialSecondRowSum_one
      (And.intro centralFactorialSecondRowSum_two
        (And.intro centralFactorialSecondRowSum_three
          (And.intro centralFactorialSecondRowSum_four
            centralFactorialSecondRowSum_five))))

theorem CentralFactorialUp_constructive_export (k : Nat) :
    centralFactorialSecond 0 k =
        BEDC.Derived.StirlingUp.stirlingSecond 0 k ∧
      centralFactorialSecond 1 k =
        BEDC.Derived.StirlingUp.stirlingSecond 1 k ∧
      Zeq (centralFactorialFirst 0 k)
        (zOfNat (BEDC.Derived.StirlingFirstUp.stirlingFirst 0 k)) ∧
      Zeq (centralFactorialFirst 1 k)
        (zOfNat (BEDC.Derived.StirlingFirstUp.stirlingFirst 1 k)) ∧
      centralFactorialSecondRowSum 5 = 12 := by
  exact And.intro (centralFactorialSecond_zero_row_stirling k)
    (And.intro (centralFactorialSecond_one_row_stirling k)
      (And.intro (centralFactorialFirst_zero_row_stirling k)
        (And.intro (centralFactorialFirst_one_row_stirling k)
          centralFactorialSecondRowSum_five)))

end BEDC.Derived.CentralFactorialUp
