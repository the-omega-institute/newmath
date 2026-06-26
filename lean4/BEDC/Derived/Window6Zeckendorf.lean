import BEDC.Derived.Window6FibonacciCount

namespace BEDC.Derived.Window6Zeckendorf

/-
Zeckendorf representations are the number-theoretic core behind the Window6
no-adjacent-one word counts: finite no-adjacent index sets select distinct
Fibonacci terms.  The Python forward proof anchors the same cylinder; this
Lean file gives the closed Nat/List induction for the shifted Fibonacci
sequence, the admissible-index interval bound, and total existence.
-/

def zfib : Nat -> Nat
  | 0 => 1
  | 1 => 2
  | n + 2 => zfib (n + 1) + zfib n

def zval : List Nat -> Nat
  | [] => 0
  | i :: is => zfib i + zval is

inductive ZReprBelow : Nat -> List Nat -> Prop
  | nil (k : Nat) : ZReprBelow k []
  | cons {k i : Nat} {is : List Nat} :
      i < k -> ZReprBelow (i - 1) is -> ZReprBelow k (i :: is)

def noAdjacent (is : List Nat) : Prop :=
  exists k : Nat, ZReprBelow k is

theorem add_left_lt_cancel_pure : forall (a r b : Nat), a + r < a + b -> r < b
  | 0, r, b, h => by
      rw [Nat.zero_add] at h
      rw [Nat.zero_add] at h
      exact h
  | a + 1, r, b, h => by
      apply add_left_lt_cancel_pure a r b
      rw [Nat.succ_add] at h
      rw [Nat.succ_add] at h
      exact Nat.lt_of_succ_lt_succ h

theorem zfib_pos : forall k : Nat, 0 < zfib k
  | 0 => Nat.zero_lt_succ 0
  | 1 => Nat.zero_lt_two
  | k + 2 => by
      rw [zfib]
      exact Nat.lt_of_lt_of_le (zfib_pos (k + 1))
        (Nat.le_add_right (zfib (k + 1)) (zfib k))

theorem zfib_succ_lt : forall k : Nat, zfib k < zfib (k + 1)
  | 0 => Nat.one_lt_two
  | 1 => by
      change 2 < 3
      exact Nat.succ_lt_succ Nat.one_lt_two
  | k + 2 => by
      change zfib (k + 1) + zfib k < zfib (k + 2) + zfib (k + 1)
      rw [zfib]
      have h1 : zfib (k + 1) + zfib k < zfib (k + 1) + zfib (k + 1) :=
        Nat.add_lt_add_left (zfib_succ_lt k) (zfib (k + 1))
      have h2 : zfib (k + 1) + zfib (k + 1) <=
          zfib (k + 1) + zfib k + zfib (k + 1) :=
        Nat.add_le_add_right
          (Nat.le_add_right (zfib (k + 1)) (zfib k))
          (zfib (k + 1))
      exact Nat.lt_of_lt_of_le h1 h2

theorem zfib_weaken_lt {k l v : Nat}
    (hkl : k <= l) (hv : v < zfib k) : v < zfib l := by
  induction hkl with
  | refl =>
      exact hv
  | step hkl ih =>
      exact Nat.lt_trans ih (zfib_succ_lt _)

theorem zfib_weaken_le {k l : Nat} (hkl : k <= l) : zfib k <= zfib l := by
  induction hkl with
  | refl =>
      exact Nat.le_refl (zfib k)
  | step hkl ih =>
      exact Nat.le_of_lt (Nat.lt_of_le_of_lt ih (zfib_succ_lt _))

theorem ZReprBelow.weaken {k l : Nat} {is : List Nat}
    (hkl : k <= l) (h : ZReprBelow k is) : ZReprBelow l is := by
  induction h with
  | nil k =>
      exact ZReprBelow.nil l
  | cons hi htail ih =>
      exact ZReprBelow.cons (Nat.lt_of_lt_of_le hi hkl) htail

theorem zval_lt_bound : forall {k : Nat} {is : List Nat},
    ZReprBelow k is -> zval is < zfib k
  | k, [], ZReprBelow.nil _ => zfib_pos k
  | 0, i :: is, ZReprBelow.cons hi _ => False.elim (Nat.not_lt_zero i hi)
  | 1, i :: is, ZReprBelow.cons hi htail => by
      cases i with
      | zero =>
          rw [Nat.zero_sub] at htail
          have htailBound : zval is < zfib 0 := zval_lt_bound htail
          rw [zfib] at htailBound
          have htailZero : zval is = 0 := by
            cases hv : zval is with
            | zero => rfl
            | succ v =>
                rw [hv] at htailBound
                exact False.elim
                  (Nat.not_lt_zero v (Nat.lt_of_succ_lt_succ htailBound))
          rw [zval, zfib, htailZero]
          exact Nat.lt_succ_self 1
      | succ i =>
          exact False.elim (Nat.not_lt_zero i (Nat.lt_of_succ_lt_succ hi))
  | k + 2, i :: is, ZReprBelow.cons hi htail => by
      cases i with
      | zero =>
          rw [Nat.zero_sub] at htail
          have htailBound : zval is < zfib 0 := zval_lt_bound htail
          rw [zval]
          have hsum : zfib 0 + zval is < zfib 1 :=
            Nat.add_lt_add_left htailBound (zfib 0)
          exact Nat.lt_of_lt_of_le hsum
            (zfib_weaken_le (Nat.succ_le_of_lt hi))
      | succ i =>
          cases i with
          | zero =>
              rw [Nat.add_one_sub_one] at htail
              have htailBound : zval is < zfib 0 := zval_lt_bound htail
              rw [zval]
              have hsum : zfib 1 + zval is < zfib 2 := by
                rw [zfib]
                exact Nat.add_lt_add_left htailBound (zfib 1)
              exact Nat.lt_of_lt_of_le hsum
                (zfib_weaken_le (Nat.succ_le_of_lt hi))
          | succ j =>
              have hlowTail : ZReprBelow (j + 1) is := by
                rw [Nat.add_one_sub_one] at htail
                exact htail
              have htailBound : zval is < zfib (j + 1) :=
                zval_lt_bound hlowTail
              rw [zval]
              have hsum : zfib (j + 2) + zval is < zfib (j + 3) := by
                change zfib (j + 2) + zval is <
                  zfib (j + 2) + zfib (j + 1)
                exact Nat.add_lt_add_left htailBound (zfib (j + 2))
              exact Nat.lt_of_lt_of_le hsum
                (zfib_weaken_le (Nat.succ_le_of_lt hi))

theorem zval_lt_next (k : Nat) {is : List Nat}
    (h : ZReprBelow (k - 1) is) : zval (k :: is) < zfib (k + 1) := by
  have hrepr : ZReprBelow (k + 1) (k :: is) :=
    ZReprBelow.cons (Nat.lt_succ_self k) h
  exact zval_lt_bound hrepr

inductive SplitAt (a n : Nat) : Type
  | left : n < a -> SplitAt a n
  | right (r : Nat) : a + r = n -> SplitAt a n

def splitAt : (a n : Nat) -> SplitAt a n
  | 0, n => SplitAt.right n (by rw [Nat.zero_add])
  | a + 1, 0 => SplitAt.left (Nat.zero_lt_succ a)
  | a + 1, n + 1 => by
      cases splitAt a n with
      | left h =>
          exact SplitAt.left (Nat.succ_lt_succ h)
      | right r hr =>
          apply SplitAt.right r
          rw [Nat.succ_add]
          exact congrArg Nat.succ hr

def greedyBelow : Nat -> Nat -> List Nat
  | 0, _ => []
  | 1, n =>
      match n with
      | 0 => []
      | _ + 1 => [0]
  | k + 2, n =>
      match splitAt (zfib (k + 1)) n with
      | SplitAt.left _ => greedyBelow (k + 1) n
      | SplitAt.right r _ => (k + 1) :: greedyBelow k r

theorem greedyBelow_spec : forall (k n : Nat), n < zfib k ->
    ZReprBelow k (greedyBelow k n) /\ zval (greedyBelow k n) = n
  | 0, n, hn => by
      cases n with
      | zero =>
          exact And.intro (ZReprBelow.nil 0) rfl
      | succ n =>
          exact False.elim (Nat.not_lt_zero n (Nat.lt_of_succ_lt_succ hn))
  | 1, n, hn => by
      cases n with
      | zero =>
          exact And.intro (ZReprBelow.nil 1) rfl
      | succ n =>
          cases n with
          | zero =>
              exact And.intro
                (ZReprBelow.cons (Nat.zero_lt_succ 0) (ZReprBelow.nil 0))
                rfl
          | succ n =>
              exact False.elim
                (Nat.not_lt_zero n (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hn)))
  | k + 2, n, hn => by
      rw [greedyBelow]
      cases hs : splitAt (zfib (k + 1)) n with
      | left hleft =>
          have hrec := greedyBelow_spec (k + 1) n hleft
          exact And.intro
            (ZReprBelow.weaken (Nat.le.step (Nat.le_refl (k + 1))) hrec.left)
            hrec.right
      | right r hr =>
          rw [zfib] at hn
          have hrBound : r < zfib k := by
            have htmp : zfib (k + 1) + r < zfib (k + 1) + zfib k := by
              rw [hr]
              exact hn
            exact add_left_lt_cancel_pure (zfib (k + 1)) r (zfib k) htmp
          have hrec := greedyBelow_spec k r hrBound
          have hadm : ZReprBelow (k + 2) ((k + 1) :: greedyBelow k r) :=
            ZReprBelow.cons (Nat.lt_succ_self (k + 1)) hrec.left
          have hval : zval ((k + 1) :: greedyBelow k r) = n := by
            rw [zval, hrec.right]
            exact hr
          exact And.intro hadm hval

theorem zfib_nat_bound (n : Nat) : n < zfib (n + 2) := by
  induction n with
  | zero =>
      exact Nat.zero_lt_succ 2
  | succ n ih =>
      have hle : n + 1 <= zfib (n + 2) := Nat.succ_le_of_lt ih
      exact Nat.lt_of_le_of_lt hle (zfib_succ_lt (n + 2))

theorem zeckendorf_exists (n : Nat) :
    exists is : List Nat, noAdjacent is /\ zval is = n := by
  have hb : n < zfib (n + 2) := zfib_nat_bound n
  have hspec := greedyBelow_spec (n + 2) n hb
  exact Exists.intro (greedyBelow (n + 2) n)
    (And.intro (Exists.intro (n + 2) hspec.left) hspec.right)

theorem zeckendorf_exists_below (k n : Nat) (hn : n < zfib k) :
    exists is : List Nat, ZReprBelow k is /\ zval is = n := by
  exact Exists.intro (greedyBelow k n) (greedyBelow_spec k n hn)

theorem zval_hundred : zval [9, 4, 2] = 100 := by
  rfl

theorem zval_one : zval [0] = 1 := by
  rfl

theorem zval_two : zval [1] = 2 := by
  rfl

theorem zval_three : zval [2] = 3 := by
  rfl

theorem zval_four : zval [2, 0] = 4 := by
  rfl

theorem zval_five : zval [3] = 5 := by
  rfl

theorem zval_six : zval [3, 0] = 6 := by
  rfl

theorem zval_seven : zval [3, 1] = 7 := by
  rfl

theorem zval_eight : zval [4] = 8 := by
  rfl

theorem zval_nine : zval [4, 0] = 9 := by
  rfl

theorem zval_ten : zval [4, 1] = 10 := by
  rfl

theorem zval_eleven : zval [4, 2] = 11 := by
  rfl

theorem zval_twelve : zval [4, 2, 0] = 12 := by
  rfl

end BEDC.Derived.Window6Zeckendorf
