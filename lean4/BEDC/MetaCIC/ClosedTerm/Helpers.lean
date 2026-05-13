import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.ClosedTerm

namespace BEDC.MetaCIC

private theorem nat_lt_add_right_closedTerm {i n : Nat} (d : Nat) (h : i < n) :
    i < n + d := by
  induction d with
  | zero => exact h
  | succ d ih =>
      rw [Nat.add_succ]
      exact Nat.lt_succ_of_lt ih

private theorem nat_add_one_add_eq_add_add_one (n d : Nat) :
    (n + 1) + d = (n + d) + 1 := by
  rw [Nat.add_assoc]
  rw [Nat.add_comm 1 d]
  rw [Nat.add_assoc]

private theorem nat_blt_true_to_lt_closedTerm (n i : Nat) :
    Nat.blt n i = true → n < i := by
  unfold Nat.blt
  intro h
  exact Nat.le_of_ble_eq_true h

private theorem nat_beq_self_true_closedTerm (n : Nat) : Nat.beq n n = true := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

private theorem closedAt_shift_any {m : Idx} {t : Term} (d : Nat)
    (h : ClosedAt m t) : (cutoff : Idx) → ClosedAt (m + d) (shift cutoff d t) := by
  induction h with
  | varClosed hlt =>
      intro cutoff
      unfold shift
      cases hble : Nat.ble cutoff _ with
      | true =>
          apply ClosedAt.varClosed
          exact Nat.add_lt_add_right hlt d
      | false =>
          apply ClosedAt.varClosed
          exact nat_lt_add_right_closedTerm d hlt
  | appClosed _ _ ihf iha =>
      intro cutoff
      unfold shift
      apply ClosedAt.appClosed
      exact ihf cutoff
      exact iha cutoff
  | lamClosed _ _ ihdom ihbody =>
      intro cutoff
      unfold shift
      apply ClosedAt.lamClosed
      exact ihdom cutoff
      rw [← nat_add_one_add_eq_add_add_one]
      exact ihbody (cutoff + 1)
  | piClosed _ _ ihdom ihcod =>
      intro cutoff
      unfold shift
      apply ClosedAt.piClosed
      exact ihdom cutoff
      rw [← nat_add_one_add_eq_add_add_one]
      exact ihcod (cutoff + 1)
  | sortClosed =>
      intro cutoff
      unfold shift
      apply ClosedAt.sortClosed

theorem closedAt_shift {n : Idx} {t : Term} (d : Nat) (h : ClosedAt n t) :
    ClosedAt (n + d) (shift n d t) := by
  exact closedAt_shift_any d h n

private theorem closedAt_substitute_var {n i : Idx} {v : Term}
    (hv : ClosedAt n v) (hlt : i < n + 1) :
    ClosedAt n (substitute n v (Term.var i)) := by
  unfold substitute
  cases hbeq : Nat.beq i n with
  | true =>
      exact hv
  | false =>
      cases hblt : Nat.blt n i with
      | true =>
          have hni : n < i := nat_blt_true_to_lt_closedTerm n i hblt
          have hle : i ≤ n := Nat.le_of_lt_succ hlt
          have hnnot : ¬ n < i := Nat.not_lt_of_ge hle
          exact False.elim (hnnot hni)
      | false =>
          apply ClosedAt.varClosed
          have hne : ¬ i = n := by
            intro heq
            rw [heq, nat_beq_self_true_closedTerm] at hbeq
            cases hbeq
          have hle : i ≤ n := Nat.le_of_lt_succ hlt
          cases Nat.lt_or_eq_of_le hle with
          | inl hlt_n => exact hlt_n
          | inr heq => exact False.elim (hne heq)

private theorem closedAt_substitute_at {depth : Idx} {t : Term}
    (h : ClosedAt depth t) : (n : Idx) → depth = n + 1 → (v : Term) →
    ClosedAt n v → ClosedAt n (substitute n v t) := by
  induction h with
  | varClosed hlt =>
      intro n hdepth v hv
      rw [hdepth] at hlt
      exact closedAt_substitute_var hv hlt
  | appClosed _ _ ihf iha =>
      intro n hdepth v hv
      unfold substitute
      apply ClosedAt.appClosed
      exact ihf n hdepth v hv
      exact iha n hdepth v hv
  | lamClosed _ _ ihdom ihbody =>
      intro n hdepth v hv
      unfold substitute
      apply ClosedAt.lamClosed
      exact ihdom n hdepth v hv
      apply ihbody (n + 1)
      rw [hdepth]
      exact closedAt_shift_any 1 hv 0
  | piClosed _ _ ihdom ihcod =>
      intro n hdepth v hv
      unfold substitute
      apply ClosedAt.piClosed
      exact ihdom n hdepth v hv
      apply ihcod (n + 1)
      rw [hdepth]
      exact closedAt_shift_any 1 hv 0
  | sortClosed =>
      intro n hdepth v hv
      unfold substitute
      apply ClosedAt.sortClosed

theorem closedAt_substitute {n : Idx} {t v : Term}
    (ht : ClosedAt (n + 1) t) (hv : ClosedAt n v) :
    ClosedAt n (substitute n v t) := by
  exact closedAt_substitute_at ht n rfl v hv

theorem closedApp_left {n : Idx} {f a : Term}
    (h : ClosedAt n (Term.app f a)) : ClosedAt n f := by
  cases h with
  | appClosed hf ha => exact hf

theorem closedApp_right {n : Idx} {f a : Term}
    (h : ClosedAt n (Term.app f a)) : ClosedAt n a := by
  cases h with
  | appClosed hf ha => exact ha

theorem closedLam_domain {n : Idx} {d b : Term}
    (h : ClosedAt n (Term.lam d b)) : ClosedAt n d := by
  cases h with
  | lamClosed hd hb => exact hd

theorem closedLam_body {n : Idx} {d b : Term}
    (h : ClosedAt n (Term.lam d b)) : ClosedAt (n + 1) b := by
  cases h with
  | lamClosed hd hb => exact hb

theorem closedPi_domain {n : Idx} {d c : Term}
    (h : ClosedAt n (Term.pi d c)) : ClosedAt n d := by
  cases h with
  | piClosed hd hc => exact hd

theorem closedPi_codomain {n : Idx} {d c : Term}
    (h : ClosedAt n (Term.pi d c)) : ClosedAt (n + 1) c := by
  cases h with
  | piClosed hd hc => exact hc

end BEDC.MetaCIC
