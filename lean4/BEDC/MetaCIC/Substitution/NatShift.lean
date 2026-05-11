import BEDC.MetaCIC.Substitution.Basic

namespace BEDC.MetaCIC

theorem nat_beq_add_one_add_one (i n : Nat) :
    Nat.beq (i + 1) (n + 1) = Nat.beq i n := by
  cases i
  · cases n
    · rfl
    · rfl
  · cases n
    · rfl
    · rfl

theorem nat_blt_add_one_add_one (n i : Nat) :
    Nat.blt (n + 1) (i + 1) = Nat.blt n i := by
  cases i
  · cases n
    · rfl
    · rfl
  · cases n
    · rfl
    · rfl

theorem nat_ble_add_one_add_one (n i : Nat) :
    Nat.ble (n + 1) (i + 1) = Nat.ble n i := by
  cases i
  · cases n
    · rfl
    · rfl
  · cases n
    · rfl
    · rfl

theorem nat_beq_false_of_ble_false (n i : Nat) :
    Nat.ble n i = false → Nat.beq i n = false := by
  induction n generalizing i with
  | zero =>
      intro h
      cases i
      · cases h
      · cases h
  | succ n ih =>
      intro h
      cases i with
      | zero => rfl
      | succ i => exact ih i h

theorem nat_blt_false_of_ble_false (n i : Nat) :
    Nat.ble n i = false → Nat.blt n i = false := by
  induction n generalizing i with
  | zero =>
      intro h
      cases i
      · cases h
      · cases h
  | succ n ih =>
      intro h
      cases i with
      | zero => rfl
      | succ i => exact ih i h

theorem nat_lt_succ_of_ble_false (d i : Nat) :
    Nat.ble d i = false → i < d + 1 := by
  induction d generalizing i with
  | zero =>
      intro h
      cases h
  | succ d ih =>
      intro h
      cases i with
      | zero =>
          exact Nat.zero_lt_succ (d + 1)
      | succ i =>
          rw [nat_ble_add_one_add_one] at h
          exact Nat.succ_lt_succ (ih i h)

theorem nat_blt_true_of_ble_true_beq_false (d i : Nat) :
    Nat.ble d i = true → Nat.beq i d = false → Nat.blt d i = true := by
  induction d generalizing i with
  | zero =>
      intro _ hbeq
      cases i with
      | zero => cases hbeq
      | succ _ => rfl
  | succ d ih =>
      intro hble hbeq
      cases i with
      | zero => cases hble
      | succ i =>
          rw [nat_ble_add_one_add_one] at hble
          rw [nat_beq_add_one_add_one] at hbeq
          rw [nat_blt_add_one_add_one]
          exact ih i hble hbeq

theorem nat_ble_pred_of_blt_succ_true (d i : Nat) :
    Nat.blt d (i + 1) = true → Nat.ble d i = true := by
  induction d generalizing i with
  | zero =>
      intro _
      rfl
  | succ d ih =>
      intro h
      cases i with
      | zero => cases h
      | succ i =>
          rw [nat_blt_add_one_add_one] at h
          rw [nat_ble_add_one_add_one]
          exact ih i h

theorem nat_beq_succ_false_of_ble_true (n i : Nat) :
    Nat.ble n i = true → Nat.beq (i + 1) n = false := by
  induction n generalizing i with
  | zero =>
      intro h
      cases i
      · rfl
      · rfl
  | succ n ih =>
      intro h
      cases i with
      | zero => cases h
      | succ i => exact ih i h

theorem nat_blt_succ_true_of_ble_true (n i : Nat) :
    Nat.ble n i = true → Nat.blt n (i + 1) = true := by
  induction n generalizing i with
  | zero =>
      intro h
      cases i
      · rfl
      · rfl
  | succ n ih =>
      intro h
      cases i with
      | zero => cases h
      | succ i => exact ih i h

theorem substitute_shift_var_at_eq (n i : Nat) (v : Term) :
    substitute n v (shift n 1 (Term.var i)) = Term.var i := by
  induction n generalizing i with
  | zero =>
      cases i
      · rfl
      · rfl
  | succ n ih =>
      cases i with
      | zero => rfl
      | succ i =>
          unfold shift
          rw [nat_ble_add_one_add_one]
          cases hble : Nat.ble n i
          · unfold substitute
            rw [nat_beq_add_one_add_one]
            rw [nat_blt_add_one_add_one]
            rw [nat_beq_false_of_ble_false n i hble]
            rw [nat_blt_false_of_ble_false n i hble]
          · unfold substitute
            rw [nat_beq_add_one_add_one]
            rw [nat_blt_add_one_add_one]
            rw [nat_beq_succ_false_of_ble_true n i hble]
            rw [nat_blt_succ_true_of_ble_true n i hble]
            rfl


end BEDC.MetaCIC
