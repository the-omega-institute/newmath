import BEDC.MetaCIC.Substitution.NatShift
import BEDC.MetaCIC.ClosedTerm

namespace BEDC.MetaCIC

/-- 任意深度替换抵消同深度的一层提升。 -/
theorem substitute_shift_at_eq (n : Idx) (v t : Term) :
    substitute n v (shift n 1 t) = t := by
  induction t generalizing n v with
  | var i =>
      exact substitute_shift_var_at_eq n i v
  | app f a ihf iha =>
      unfold shift
      unfold substitute
      rw [ihf, iha]
  | lam d b ihd ihb =>
      unfold shift
      unfold substitute
      rw [ihd, ihb]
  | pi d c ihd ihc =>
      unfold shift
      unfold substitute
      rw [ihd, ihc]
  | sort =>
      rfl

theorem substitute_closed_via_term_induction
    (d : Idx) (v t : Term) (h : ClosedAt d t) :
    substitute d v t = t := by
  induction t generalizing d v with
  | var i =>
      cases h with
      | varClosed hlt =>
          unfold substitute
          rw [nat_beq_false_of_lt _ _ hlt]
          rw [nat_blt_false_of_lt _ _ hlt]
  | app f a ihf iha =>
      cases h with
      | appClosed hf ha =>
          unfold substitute
          rw [ihf d v hf, iha d v ha]
  | lam dom body ihdom ihbody =>
      cases h with
      | lamClosed hdom hbody =>
          unfold substitute
          rw [ihdom d v hdom]
          rw [ihbody (d + 1) (shift 0 1 v) hbody]
  | pi dom cod ihdom ihcod =>
      cases h with
      | piClosed hdom hcod =>
          unfold substitute
          rw [ihdom d v hdom]
          rw [ihcod (d + 1) (shift 0 1 v) hcod]
  | sort =>
      rfl

theorem closedAt_succ (d : Idx) (t : Term) :
    ClosedAt d t → ClosedAt (d + 1) t := by
  intro h
  induction h with
  | varClosed hlt =>
      apply ClosedAt.varClosed
      exact Nat.lt_trans hlt (Nat.lt_succ_self _)
  | appClosed _ _ ihf iha =>
      apply ClosedAt.appClosed
      · exact ihf
      · exact iha
  | lamClosed _ _ ihdom ihbody =>
      apply ClosedAt.lamClosed
      · exact ihdom
      · exact ihbody
  | piClosed _ _ ihdom ihcod =>
      apply ClosedAt.piClosed
      · exact ihdom
      · exact ihcod
  | sortClosed =>
      exact ClosedAt.sortClosed

theorem closedAt_zero_at (d : Idx) (t : Term) :
    ClosedAt 0 t → ClosedAt d t := by
  induction d with
  | zero =>
      intro h
      exact h
  | succ d ih =>
      intro h
      exact closedAt_succ d t (ih h)

theorem shift_substitute_var_closed_at_zero
    (d i : Idx) (s : Term) (hclosed_s : ClosedAt 0 s) :
    shift d 1 (substitute d s (Term.var i)) =
      substitute (d + 1) s (shift d 1 (Term.var i)) := by
  cases hble : Nat.ble d i
  · have hlt : i < d + 1 := nat_lt_succ_of_ble_false d i hble
    have hbeq : Nat.beq i d = false :=
      nat_beq_false_of_ble_false d i hble
    have hblt : Nat.blt d i = false :=
      nat_blt_false_of_ble_false d i hble
    change shift d 1
        (match Nat.beq i d, Nat.blt d i with
        | true, _ => s
        | false, true => Term.var (i - 1)
        | false, false => Term.var i) =
      substitute (d + 1) s
        (match Nat.ble d i with
        | true => Term.var (i + 1)
        | false => Term.var i)
    rw [hbeq, hblt, hble]
    change shift d 1 (Term.var i) = substitute (d + 1) s (Term.var i)
    change
      (match Nat.ble d i with
      | true => Term.var (i + 1)
      | false => Term.var i) =
        (match Nat.beq i (d + 1), Nat.blt (d + 1) i with
        | true, _ => s
        | false, true => Term.var (i - 1)
        | false, false => Term.var i)
    rw [hble]
    rw [nat_beq_false_of_lt _ _ hlt]
    rw [nat_blt_false_of_lt _ _ hlt]
  · change shift d 1
        (match Nat.beq i d, Nat.blt d i with
        | true, _ => s
        | false, true => Term.var (i - 1)
        | false, false => Term.var i) =
      substitute (d + 1) s
        (match Nat.ble d i with
        | true => Term.var (i + 1)
        | false => Term.var i)
    rw [hble]
    cases hbeq : Nat.beq i d
    · have hblt : Nat.blt d i = true :=
        nat_blt_true_of_ble_true_beq_false d i hble hbeq
      rw [hblt]
      cases i with
      | zero =>
          cases hblt
      | succ i =>
          change shift d 1 (Term.var (i + 1 - 1)) =
            substitute (d + 1) s (Term.var (i + 1 + 1))
          change
            (match Nat.ble d (i + 1 - 1) with
            | true => Term.var (i + 1 - 1 + 1)
            | false => Term.var (i + 1 - 1)) =
              (match Nat.beq (i + 1 + 1) (d + 1),
                  Nat.blt (d + 1) (i + 1 + 1) with
              | true, _ => s
              | false, true => Term.var (i + 1 + 1 - 1)
              | false, false => Term.var (i + 1 + 1))
          rw [Nat.succ_sub_one]
          rw [nat_ble_pred_of_blt_succ_true d i hblt]
          rw [nat_beq_add_one_add_one]
          rw [nat_blt_add_one_add_one]
          rw [hbeq]
          rw [hblt]
          rfl
    · change shift d 1 s = substitute (d + 1) s (Term.var (i + 1))
      rw [shift_closed d s (closedAt_zero_at d s hclosed_s)]
      change s =
        (match Nat.beq (i + 1) (d + 1), Nat.blt (d + 1) (i + 1) with
        | true, _ => s
        | false, true => Term.var (i + 1 - 1)
        | false, false => Term.var (i + 1))
      rw [nat_beq_add_one_add_one]
      rw [hbeq]

theorem shift_substitute_at_closed_zero
    (d : Idx) (s a : Term) (hclosed_s : ClosedAt 0 s) :
    shift d 1 (substitute d s a) =
      substitute (d + 1) s (shift d 1 a) := by
  induction a generalizing d s with
  | var i =>
      exact shift_substitute_var_closed_at_zero d i s hclosed_s
  | app f a ihf iha =>
      change
        Term.app (shift d 1 (substitute d s f))
            (shift d 1 (substitute d s a)) =
          Term.app (substitute (d + 1) s (shift d 1 f))
            (substitute (d + 1) s (shift d 1 a))
      rw [ihf d s hclosed_s]
      rw [iha d s hclosed_s]
  | lam dom body ihdom ihbody =>
      change
        Term.lam (shift d 1 (substitute d s dom))
            (shift (d + 1) 1
              (substitute (d + 1) (shift 0 1 s) body)) =
          Term.lam (substitute (d + 1) s (shift d 1 dom))
            (substitute (d + 1 + 1) (shift 0 1 s)
              (shift (d + 1) 1 body))
      rw [shift_closed 0 s hclosed_s]
      rw [ihdom d s hclosed_s]
      rw [ihbody (d + 1) s hclosed_s]
  | pi dom cod ihdom ihcod =>
      change
        Term.pi (shift d 1 (substitute d s dom))
            (shift (d + 1) 1
              (substitute (d + 1) (shift 0 1 s) cod)) =
          Term.pi (substitute (d + 1) s (shift d 1 dom))
            (substitute (d + 1 + 1) (shift 0 1 s)
              (shift (d + 1) 1 cod))
      rw [shift_closed 0 s hclosed_s]
      rw [ihdom d s hclosed_s]
      rw [ihcod (d + 1) s hclosed_s]
  | sort =>
      rfl

theorem shift_substitute_zero_zero_closed
    (s a : Term)
    (hclosed_s : ClosedAt 0 s) :
    shift 0 1 (substitute 0 s a) =
      substitute 1 (shift 0 1 s) (shift 0 1 a) := by
  rw [shift_closed 0 s hclosed_s]
  exact shift_substitute_at_closed_zero 0 s a hclosed_s

theorem nat_succ_lt_of_beq_false_blt_false_succ_lt (d i : Nat) :
    Nat.beq i d = false →
    Nat.blt d i = false →
    i < d + 1 →
    i + 1 < d + 1 := by
  induction d generalizing i with
  | zero =>
      intro hbeq hblt hlt
      cases i with
      | zero =>
          cases hbeq
      | succ i =>
          exact False.elim (Nat.not_lt_zero i (Nat.lt_of_succ_lt_succ hlt))
  | succ d ih =>
      intro hbeq hblt hlt
      cases i with
      | zero =>
          exact Nat.succ_lt_succ (Nat.zero_lt_succ d)
      | succ i =>
          rw [nat_beq_add_one_add_one] at hbeq
          rw [nat_blt_add_one_add_one] at hblt
          exact Nat.succ_lt_succ
            (ih i hbeq hblt (Nat.lt_of_succ_lt_succ hlt))

theorem substitute_var_closed_boundary
    (d i : Idx) (s : Term)
    (hs : ClosedAt d s)
    (hlt : i < d + 1) :
    ClosedAt d (substitute d s (Term.var i)) := by
  induction d generalizing i with
  | zero =>
      cases i with
      | zero =>
          unfold substitute
          exact hs
      | succ i =>
          exact False.elim (Nat.not_lt_zero i (Nat.lt_of_succ_lt_succ hlt))
  | succ d ih =>
      cases i with
      | zero =>
          unfold substitute
          apply ClosedAt.varClosed
          exact Nat.zero_lt_succ d
      | succ i =>
          unfold substitute
          rw [nat_beq_add_one_add_one]
          rw [nat_blt_add_one_add_one]
          cases hbeq : Nat.beq i d
          · cases hblt : Nat.blt d i
            · apply ClosedAt.varClosed
              exact nat_succ_lt_of_beq_false_blt_false_succ_lt d i
                hbeq hblt (Nat.lt_of_succ_lt_succ hlt)
            · apply ClosedAt.varClosed
              exact Nat.lt_of_succ_lt_succ hlt
          · exact hs

theorem substitute_closed_source_closes_anchor_via_term_induction
    (d : Idx) {s t : Term}
    (hclosed_s : ClosedAt 0 s)
    (hclosed_t : ClosedAt (d + 1) t) :
    ClosedAt d (substitute d s t) := by
  induction t generalizing d with
  | var i =>
      cases hclosed_t with
      | varClosed hlt =>
          exact substitute_var_closed_boundary d i s
            (closedAt_zero_at d s hclosed_s) hlt
  | app f a ihf iha =>
      cases hclosed_t with
      | appClosed hf ha =>
          unfold substitute
          apply ClosedAt.appClosed
          · exact ihf d hf
          · exact iha d ha
  | lam dom body ihdom ihbody =>
      cases hclosed_t with
      | lamClosed hdom hbody =>
          unfold substitute
          rw [shift_closed 0 s hclosed_s]
          apply ClosedAt.lamClosed
          · exact ihdom d hdom
          · exact ihbody (d + 1) hbody
  | pi dom cod ihdom ihcod =>
      cases hclosed_t with
      | piClosed hdom hcod =>
          unfold substitute
          rw [shift_closed 0 s hclosed_s]
          apply ClosedAt.piClosed
          · exact ihdom d hdom
          · exact ihcod (d + 1) hcod
  | sort =>
      exact ClosedAt.sortClosed

theorem substitute_substitute_zero_zero_unclosed_counterexample :
    substitute 0 (Term.var 0)
        (substitute 0 Term.sort (Term.var 1)) ≠
      substitute 0 (substitute 0 (Term.var 0) Term.sort)
        (substitute 1 (Term.var 0) (Term.var 1)) := by
  intro h
  cases h

theorem substitute_substitute_zero_zero_closed_sort
    (s a : Term)
    (_hclosed_s : ClosedAt 0 s) :
    substitute 0 s (substitute 0 a Term.sort) =
      substitute 0 (substitute 0 s a) (substitute 1 s Term.sort) := by
  rfl

theorem substitute_substitute_zero_zero_closed_var
    (s a : Term) (i : Idx)
    (hclosed_s : ClosedAt 0 s) :
    substitute 0 s (substitute 0 a (Term.var i)) =
      substitute 0 (substitute 0 s a) (substitute 1 s (Term.var i)) := by
  cases i with
  | zero =>
      rfl
  | succ i =>
      cases i with
      | zero =>
          rw [substitute_var_succ_zero a 0]
          rw [substitute_var_zero s]
          rw [substitute_var_one s]
          change s = substitute 0 (substitute 0 s a) s
          rw [substitute_closed 0 (substitute 0 s a) s hclosed_s]
      | succ i =>
          unfold substitute
          rfl

theorem substitute_substitute_zero_zero_closed_app
    (s a f b : Term)
    (hf :
      substitute 0 s (substitute 0 a f) =
        substitute 0 (substitute 0 s a) (substitute 1 s f))
    (hb :
      substitute 0 s (substitute 0 a b) =
        substitute 0 (substitute 0 s a) (substitute 1 s b)) :
    substitute 0 s (substitute 0 a (Term.app f b)) =
      substitute 0 (substitute 0 s a)
        (substitute 1 s (Term.app f b)) := by
  change
    Term.app (substitute 0 s (substitute 0 a f))
        (substitute 0 s (substitute 0 a b)) =
      Term.app
        (substitute 0 (substitute 0 s a) (substitute 1 s f))
        (substitute 0 (substitute 0 s a) (substitute 1 s b))
  rw [hf]
  rw [hb]

theorem substitute_substitute_zero_zero_lam_closed_anchor
    (s a dom body : Term)
    (_hclosed_s : ClosedAt 0 s)
    (hshift :
      shift 0 1 (substitute 0 s a) =
        substitute 1 (shift 0 1 s) (shift 0 1 a))
    (hdom :
      substitute 0 s (substitute 0 a dom) =
        substitute 0 (substitute 0 s a) (substitute 1 s dom))
    (hbody :
      substitute 1 (shift 0 1 s)
          (substitute 1 (shift 0 1 a) body) =
        substitute 1
          (substitute 1 (shift 0 1 s) (shift 0 1 a))
          (substitute 2 (shift 0 1 s) body)) :
    substitute 0 s (substitute 0 a (Term.lam dom body)) =
      substitute 0 (substitute 0 s a)
        (substitute 1 s (Term.lam dom body)) := by
  change
    Term.lam
        (substitute 0 s (substitute 0 a dom))
        (substitute 1 (shift 0 1 s)
          (substitute 1 (shift 0 1 a) body)) =
      Term.lam
        (substitute 0 (substitute 0 s a) (substitute 1 s dom))
        (substitute 1 (shift 0 1 (substitute 0 s a))
          (substitute 2 (shift 0 1 s) body))
  rw [hdom]
  rw [hshift]
  rw [hbody]

theorem substitute_substitute_zero_zero_pi_closed_anchor
    (s a dom cod : Term)
    (_hclosed_s : ClosedAt 0 s)
    (hshift :
      shift 0 1 (substitute 0 s a) =
        substitute 1 (shift 0 1 s) (shift 0 1 a))
    (hdom :
      substitute 0 s (substitute 0 a dom) =
        substitute 0 (substitute 0 s a) (substitute 1 s dom))
    (hcod :
      substitute 1 (shift 0 1 s)
          (substitute 1 (shift 0 1 a) cod) =
        substitute 1
          (substitute 1 (shift 0 1 s) (shift 0 1 a))
          (substitute 2 (shift 0 1 s) cod)) :
    substitute 0 s (substitute 0 a (Term.pi dom cod)) =
      substitute 0 (substitute 0 s a)
        (substitute 1 s (Term.pi dom cod)) := by
  change
    Term.pi
        (substitute 0 s (substitute 0 a dom))
        (substitute 1 (shift 0 1 s)
          (substitute 1 (shift 0 1 a) cod)) =
      Term.pi
        (substitute 0 (substitute 0 s a) (substitute 1 s dom))
        (substitute 1 (shift 0 1 (substitute 0 s a))
          (substitute 2 (shift 0 1 s) cod))
  rw [hdom]
  rw [hshift]
  rw [hcod]


end BEDC.MetaCIC
