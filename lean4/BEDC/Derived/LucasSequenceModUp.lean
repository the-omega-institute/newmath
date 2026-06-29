import BEDC.Derived.LucasUVSequenceUp

namespace BEDC.Derived.LucasSequenceModUp

abbrev lucasU : Int -> Int -> Nat -> Int :=
  BEDC.Derived.LucasUVSequenceUp.lucasU

abbrev lucasV : Int -> Int -> Nat -> Int :=
  BEDC.Derived.LucasUVSequenceUp.lucasV

def signedResidue (m : Nat) (z : Int) : Nat :=
  match z with
  | Int.ofNat n => n % m
  | Int.negSucc n =>
      match m with
      | 0 => 0
      | Nat.succ mm => (Nat.succ mm - (Nat.succ n % Nat.succ mm)) % Nat.succ mm

structure LucasModState where
  u : Nat
  uNext : Nat
  v : Nat
  vNext : Nat
deriving DecidableEq

def lucasRawModState (P Q : Int) (m : Nat) (n : Nat) : LucasModState :=
  { u := signedResidue m (lucasU P Q n)
    uNext := signedResidue m (lucasU P Q (n + 1))
    v := signedResidue m (lucasV P Q n)
    vNext := signedResidue m (lucasV P Q (n + 1)) }

def nextLucasModState (P Q : Int) (m : Nat) (s : LucasModState) : LucasModState :=
  { u := s.uNext
    uNext := signedResidue m (P * Int.ofNat s.uNext - Q * Int.ofNat s.u)
    v := s.vNext
    vNext := signedResidue m (P * Int.ofNat s.vNext - Q * Int.ofNat s.v) }

def lucasModState (P Q : Int) (m : Nat) : Nat -> LucasModState
  | 0 =>
      { u := signedResidue m 0
        uNext := signedResidue m 1
        v := signedResidue m 2
        vNext := signedResidue m P }
  | n + 1 => nextLucasModState P Q m (lucasModState P Q m n)

theorem lucasModState_step (P Q : Int) (m n : Nat) :
    lucasModState P Q m (n + 1) =
      nextLucasModState P Q m (lucasModState P Q m n) := by
  rfl

def LucasReturn (P Q : Int) (m k : Nat) : Prop :=
  0 < m ∧ 0 < k ∧ lucasModState P Q m k = lucasModState P Q m 0

def LucasReturnCycle (P Q : Int) (m k : Nat) : Prop :=
  0 < m ∧ 0 < k ∧
    ∀ t : Nat, lucasModState P Q m (t + k) = lucasModState P Q m t

def LucasEventualCycle (P Q : Int) (m start period : Nat) : Prop :=
  0 < m ∧ 0 < period ∧
    ∀ t : Nat,
      lucasModState P Q m (start + t + period) =
        lucasModState P Q m (start + t)

def LucasStateRepeat (P Q : Int) (m start period : Nat) : Prop :=
  0 < m ∧ 0 < period ∧
    lucasModState P Q m (start + period) = lucasModState P Q m start

def lucasStateSpace (m : Nat) : List LucasModState :=
  List.flatMap
    (fun a =>
      List.flatMap
        (fun b =>
          List.flatMap
            (fun c =>
              (List.range m).map
                (fun d => { u := a, uNext := b, v := c, vNext := d }))
            (List.range m))
        (List.range m))
    (List.range m)

theorem signedResidue_lt {m : Nat} (z : Int) :
    0 < m -> signedResidue m z < m := by
  intro mPositive
  cases z with
  | ofNat n =>
      unfold signedResidue
      exact Nat.mod_lt n mPositive
  | negSucc n =>
      cases m with
      | zero =>
          cases mPositive
      | succ mm =>
          unfold signedResidue
          exact Nat.mod_lt (Nat.succ mm - (Nat.succ n % Nat.succ mm))
            (Nat.succ_pos mm)

theorem lucasModState_bounded {P Q : Int} {m n : Nat} :
    0 < m ->
      (lucasModState P Q m n).u < m ∧
        (lucasModState P Q m n).uNext < m ∧
          (lucasModState P Q m n).v < m ∧
            (lucasModState P Q m n).vNext < m := by
  intro mPositive
  induction n with
  | zero =>
      exact ⟨signedResidue_lt 0 mPositive,
        ⟨signedResidue_lt 1 mPositive,
          ⟨signedResidue_lt 2 mPositive, signedResidue_lt P mPositive⟩⟩⟩
  | succ n ih =>
      exact ⟨ih.right.left,
        ⟨signedResidue_lt
            (P * Int.ofNat (lucasModState P Q m n).uNext -
              Q * Int.ofNat (lucasModState P Q m n).u)
            mPositive,
          ⟨ih.right.right.right,
            signedResidue_lt
              (P * Int.ofNat (lucasModState P Q m n).vNext -
                Q * Int.ofNat (lucasModState P Q m n).v)
              mPositive⟩⟩⟩

theorem lucasModState_finite_envelope {P Q : Int} {m n : Nat} :
    0 < m ->
      (lucasModState P Q m n).u < m ∧
        (lucasModState P Q m n).uNext < m ∧
          (lucasModState P Q m n).v < m ∧
            (lucasModState P Q m n).vNext < m :=
  lucasModState_bounded

def noReturnBeforeFrom (P Q : Int) (m j fuel : Nat) : Bool :=
  match fuel with
  | 0 => true
  | f + 1 =>
      if lucasModState P Q m j = lucasModState P Q m 0 then
        false
      else
        noReturnBeforeFrom P Q m (j + 1) f

def noReturnBefore (P Q : Int) (m k : Nat) : Bool :=
  noReturnBeforeFrom P Q m 1 (k - 1)

theorem noReturnBeforeFrom_sound {P Q : Int} {m j fuel : Nat} :
    noReturnBeforeFrom P Q m j fuel = true ->
      ∀ r : Nat, j ≤ r -> r < j + fuel ->
        lucasModState P Q m r ≠ lucasModState P Q m 0 := by
  intro checked
  induction fuel generalizing j with
  | zero =>
      intro r jLeR rLt eqState
      rw [Nat.add_zero] at rLt
      exact False.elim ((Nat.not_lt_of_ge jLeR) rLt)
  | succ fuel ih =>
      intro r jLeR rLt eqState
      unfold noReturnBeforeFrom at checked
      by_cases current : lucasModState P Q m j = lucasModState P Q m 0
      · rw [if_pos current] at checked
        cases checked
      · rw [if_neg current] at checked
        cases Nat.lt_or_ge r (j + 1) with
        | inl rLtSucc =>
            have notRLtJ : ¬r < j := Nat.not_lt_of_ge jLeR
            have rEqJ : r = j := Nat.eq_of_lt_succ_of_not_lt rLtSucc notRLtJ
            exact current (by rw [← rEqJ]; exact eqState)
        | inr succLeR =>
            exact ih checked r succLeR
              (by
                change r < j + (fuel + 1) at rLt
                change r < (j + 1) + fuel
                have boundShape : j + (fuel + 1) = (j + 1) + fuel := by
                  rw [Nat.add_comm fuel 1]
                  rw [← Nat.add_assoc]
                rw [boundShape] at rLt
                exact rLt)
              eqState

theorem noReturnBefore_sound {P Q : Int} {m k : Nat} :
    noReturnBefore P Q m k = true ->
      ∀ r : Nat, 0 < r -> r < k ->
        lucasModState P Q m r ≠ lucasModState P Q m 0 := by
  intro checked r rPositive rLt eqState
  unfold noReturnBefore at checked
  cases k with
  | zero =>
      exact False.elim ((Nat.not_lt_zero r) rLt)
  | succ k =>
      exact noReturnBeforeFrom_sound checked r rPositive
        (by
          change r < k + 1 at rLt
          change r < 1 + k
          rw [Nat.add_comm] at rLt
          exact rLt)
        eqState

def LucasReturnPeriod (P Q : Int) (m k : Nat) : Prop :=
  LucasReturnCycle P Q m k ∧
    ∀ j : Nat, 0 < j -> j < k ->
      lucasModState P Q m j ≠ lucasModState P Q m 0

theorem lucasReturnPeriod_of_checked {P Q : Int} {m k : Nat} :
    LucasReturnCycle P Q m k ->
      noReturnBefore P Q m k = true ->
        LucasReturnPeriod P Q m k := by
  intro cycle checked
  exact ⟨cycle, noReturnBefore_sound checked⟩

theorem lucas_cycle_of_return {P Q : Int} {m k : Nat} :
    LucasReturn P Q m k -> LucasReturnCycle P Q m k := by
  intro ret
  refine ⟨ret.left, ret.right.left, ?_⟩
  intro t
  induction t with
  | zero =>
      rw [Nat.zero_add]
      exact ret.right.right
  | succ t ih =>
      calc
        lucasModState P Q m (Nat.succ t + k) =
            nextLucasModState P Q m (lucasModState P Q m (t + k)) := by
          rw [show Nat.succ t + k = (t + k) + 1 by
            rw [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 k, ← Nat.add_assoc]]
          exact lucasModState_step P Q m (t + k)
        _ = nextLucasModState P Q m (lucasModState P Q m t) := by
          rw [ih]
        _ = lucasModState P Q m (Nat.succ t) := by
          change nextLucasModState P Q m (lucasModState P Q m t) =
            lucasModState P Q m (t + 1)
          exact (lucasModState_step P Q m t).symm

theorem lucas_eventual_cycle_of_state_repeat {P Q : Int} {m start period : Nat} :
    LucasStateRepeat P Q m start period -> LucasEventualCycle P Q m start period := by
  intro rep
  refine ⟨rep.left, rep.right.left, ?_⟩
  intro t
  induction t with
  | zero =>
      rw [Nat.add_zero]
      exact rep.right.right
  | succ t ih =>
      calc
        lucasModState P Q m (start + Nat.succ t + period) =
            nextLucasModState P Q m
              (lucasModState P Q m (start + t + period)) := by
          rw [show start + Nat.succ t + period = (start + t + period) + 1 by
            rw [Nat.succ_eq_add_one]
            calc
              start + (t + 1) + period =
                  (start + t + 1) + period := by
                rw [← Nat.add_assoc start t 1]
              _ = start + t + (1 + period) := by
                rw [Nat.add_assoc (start + t) 1 period]
              _ = start + t + (period + 1) := by
                rw [Nat.add_comm 1 period]
              _ = start + t + period + 1 := by
                rw [← Nat.add_assoc (start + t) period 1]]
          exact lucasModState_step P Q m (start + t + period)
        _ =
            nextLucasModState P Q m
              (lucasModState P Q m (start + t)) := by
          rw [ih]
        _ = lucasModState P Q m (start + Nat.succ t) := by
          rw [show start + Nat.succ t = (start + t) + 1 by
            rw [Nat.succ_eq_add_one]
            rw [← Nat.add_assoc start t 1]]
          exact (lucasModState_step P Q m (start + t)).symm

def LucasIntDivides (a b : Int) : Prop :=
  ∃ c : Int, b = a * c

theorem lucasIntDivides_refl (a : Int) :
    LucasIntDivides a a := by
  exact ⟨1, by
    cases a with
    | ofNat n =>
        change Int.ofNat n = Int.ofNat (n * 1)
        rw [Nat.mul_one]
    | negSucc n =>
        change Int.negSucc n = Int.negOfNat ((n + 1) * 1)
        rw [Nat.mul_one]
        rfl⟩

theorem lucasIntDivides_zero_right (a : Int) :
    LucasIntDivides a 0 := by
  exact ⟨0, by rw [Int.mul_zero]⟩

theorem lucasU_divides_lucasU_self (P Q : Int) (n : Nat) :
    LucasIntDivides (lucasU P Q n) (lucasU P Q n) :=
  lucasIntDivides_refl (lucasU P Q n)

theorem lucasU_divides_lucasU_zero_multiple (P Q : Int) (n : Nat) :
    LucasIntDivides (lucasU P Q n) (lucasU P Q (0 * n)) := by
  rw [Nat.zero_mul]
  change LucasIntDivides (lucasU P Q n) 0
  exact lucasIntDivides_zero_right (lucasU P Q n)

theorem lucasU_divides_lucasU_one_multiple (P Q : Int) (n : Nat) :
    LucasIntDivides (lucasU P Q n) (lucasU P Q (1 * n)) := by
  rw [Nat.one_mul]
  exact lucasIntDivides_refl (lucasU P Q n)

theorem lucasU_divides_lucasU_mul_index_window (P Q : Int) (n k : Nat) :
    k = 0 ∨ k = 1 ->
      LucasIntDivides (lucasU P Q n) (lucasU P Q (k * n)) := by
  intro hk
  cases hk with
  | inl kZero =>
      rw [kZero]
      exact lucasU_divides_lucasU_zero_multiple P Q n
  | inr kOne =>
      rw [kOne]
      exact lucasU_divides_lucasU_one_multiple P Q n

theorem lucasU_divides_lucasU_multiple_finite_window :
    LucasIntDivides (lucasU 1 (-1) 2) (lucasU 1 (-1) (3 * 2)) ∧
      LucasIntDivides (lucasU 1 (-1) 3) (lucasU 1 (-1) (2 * 3)) ∧
        LucasIntDivides (lucasU 1 (-1) 4) (lucasU 1 (-1) (3 * 4)) ∧
          LucasIntDivides (lucasU 2 (-1) 2) (lucasU 2 (-1) (3 * 2)) ∧
            LucasIntDivides (lucasU 2 (-1) 3) (lucasU 2 (-1) (2 * 3)) ∧
              LucasIntDivides (lucasU 2 (-1) 4) (lucasU 2 (-1) (3 * 4)) := by
  exact ⟨⟨8, by decide⟩,
    ⟨⟨4, by decide⟩,
      ⟨⟨48, by decide⟩,
        ⟨⟨35, by decide⟩,
          ⟨⟨14, by decide⟩,
            ⟨1155, by decide⟩⟩⟩⟩⟩⟩

theorem fibonacci_lucas_return_two_three : LucasReturn 1 (-1) 2 3 := by
  exact ⟨by decide, ⟨by decide, by decide⟩⟩

theorem fibonacci_lucas_cycle_two_three : LucasReturnCycle 1 (-1) 2 3 :=
  lucas_cycle_of_return fibonacci_lucas_return_two_three

theorem fibonacci_lucas_eventual_cycle_two_three : LucasEventualCycle 1 (-1) 2 0 3 :=
  lucas_eventual_cycle_of_state_repeat
    ⟨by decide, ⟨by decide, by decide⟩⟩

theorem fibonacci_lucas_return_period_two_three : LucasReturnPeriod 1 (-1) 2 3 :=
  lucasReturnPeriod_of_checked fibonacci_lucas_cycle_two_three (by rfl)

theorem fibonacci_lucas_period_exists_mod_two :
    ∃ k : Nat, LucasReturnPeriod 1 (-1) 2 k :=
  ⟨3, fibonacci_lucas_return_period_two_three⟩

theorem fibonacci_lucas_return_three_eight : LucasReturn 1 (-1) 3 8 := by
  exact ⟨by decide, ⟨by decide, by decide⟩⟩

theorem fibonacci_lucas_cycle_three_eight : LucasReturnCycle 1 (-1) 3 8 :=
  lucas_cycle_of_return fibonacci_lucas_return_three_eight

theorem fibonacci_lucas_eventual_cycle_three_eight : LucasEventualCycle 1 (-1) 3 0 8 :=
  lucas_eventual_cycle_of_state_repeat
    ⟨by decide, ⟨by decide, by decide⟩⟩

theorem fibonacci_lucas_return_period_three_eight : LucasReturnPeriod 1 (-1) 3 8 :=
  lucasReturnPeriod_of_checked fibonacci_lucas_cycle_three_eight (by rfl)

theorem fibonacci_lucas_period_exists_mod_three :
    ∃ k : Nat, LucasReturnPeriod 1 (-1) 3 k :=
  ⟨8, fibonacci_lucas_return_period_three_eight⟩

theorem pell_lucas_return_two_four : LucasReturn 2 (-1) 2 4 := by
  exact ⟨by decide, ⟨by decide, by decide⟩⟩

theorem pell_lucas_cycle_two_four : LucasReturnCycle 2 (-1) 2 4 :=
  lucas_cycle_of_return pell_lucas_return_two_four

theorem pell_lucas_period_exists_mod_two :
    ∃ k : Nat, LucasReturnCycle 2 (-1) 2 k :=
  ⟨4, pell_lucas_cycle_two_four⟩

theorem mersenne_lucas_return_five_four : LucasReturn 3 2 5 4 := by
  exact ⟨by decide, ⟨by decide, by decide⟩⟩

theorem mersenne_lucas_cycle_five_four : LucasReturnCycle 3 2 5 4 :=
  lucas_cycle_of_return mersenne_lucas_return_five_four

theorem mersenne_lucas_period_exists_mod_five :
    ∃ k : Nat, LucasReturnCycle 3 2 5 k :=
  ⟨4, mersenne_lucas_cycle_five_four⟩

def lucasModSmallPrimeWitnesses : List Nat :=
  [2, 3, 5, 7, 11, 13]

theorem fibonacci_lucas_v_small_prime_mod_window :
    lucasModSmallPrimeWitnesses.all
      (fun p =>
        signedResidue p (lucasV 1 (-1) p) == (1 % p)) = true := by
  decide

theorem fibonacci_lucas_u_small_prime_mod_window :
    ([2, 3, 7, 11, 13] : List Nat).all
      (fun p =>
        signedResidue p (lucasU 1 (-1) p) ==
          (if p % 5 == 1 || p % 5 == 4 then 1 else p - 1)) = true := by
  decide

end BEDC.Derived.LucasSequenceModUp
