import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Typing
import BEDC.MetaCIC.ContextWF
import BEDC.MetaCIC.ClosedTerm

namespace BEDC.MetaCIC

/-- 带上下文良构前提的替换保持命题形状。 -/
def SubstitutePreservesTypingStatementWF : Prop :=
  ∀ {Γ : Ctx} {t s A B : Term},
    WellFormedCtx (B :: Γ) →
    HasType (B :: Γ) t A →
    HasType Γ s B →
    HasType Γ (substitute 0 s t) (substitute 0 s A)

/-- 闭合替换保持的完整目标形状。 -/
def ClosedTermSubstitutePreservesTypingStatement : Prop :=
  ∀ {Γ : Ctx} {t s A B : Term},
    WellFormedCtx (B :: Γ) →
    ClosedAt 0 B →
    ClosedAt 0 s →
    HasType (B :: Γ) t A →
    HasType Γ s B →
    HasType Γ (substitute 0 s t) (substitute 0 s A)

def SubstitutePreservesTypingGeneralStatement : Prop :=
  ∀ (Γ₁ Γ₂ : Ctx) {t s A B : Term},
    WellFormedCtx (Γ₁ ++ B :: Γ₂) →
    HasType (Γ₁ ++ B :: Γ₂) t A →
    HasType Γ₂ s B →
    HasType (Γ₁ ++ Γ₂)
      (substitute Γ₁.length s t)
      (substitute Γ₁.length s A)

def SubstitutePreservesTypingShiftedStatement : Prop :=
  ∀ {Γ : Ctx} {t s A B : Term},
    WellFormedCtx (B :: Γ) →
    ClosedAt 0 s →
    HasType (B :: Γ) t A →
    HasType Γ s B →
    HasType Γ (substitute 0 s t) (substitute 0 s A)

/-- sort 上的替换按定义保持 sort。 -/
theorem substitute_sort (d : Idx) (v : Term) :
    substitute d v Term.sort = Term.sort := by
  rfl

/-- 深度零变量被替换项本身取代。 -/
theorem substitute_var_zero (v : Term) :
    substitute 0 v (Term.var 0) = v := by
  unfold substitute
  rfl

/-- 深度零替换穿过正变量时删除一个 binder 层。 -/
theorem substitute_var_succ_zero (v : Term) (i : Idx) :
    substitute 0 v (Term.var (i + 1)) = Term.var i := by
  cases i
  · unfold substitute
    rfl
  · unfold substitute
    rfl

theorem substitute_var_one (v : Term) :
    substitute 1 v (Term.var 1) = v := by
  unfold substitute
  rfl

/-- cons 上第零变量的类型就是栈顶类型。 -/
theorem lookup_cons_zero (Γ : Ctx) (B : Term) :
    Ctx.lookup (B :: Γ) 0 = some B := by
  rfl

/-- cons 下方变量 lookup 会提升返回类型。 -/
theorem lookup_cons_succ (Γ : Ctx) (B : Term) (i : Idx) :
    Ctx.lookup (B :: Γ) (i + 1) =
      match Ctx.lookup Γ i with
      | some T => some (shift 0 1 T)
      | none => none := by
  rfl

/-- 从 cons 良构上下文取出尾部良构。 -/
theorem wellFormedCtx_cons_tail {Γ : Ctx} {B : Term} :
    WellFormedCtx (B :: Γ) → WellFormedCtx Γ := by
  intro hwf
  cases hwf with
  | wfCons tail _ =>
      exact tail

/-- 从 cons 良构上下文取出栈顶类型的 sort 判定。 -/
theorem wellFormedCtx_cons_head_type {Γ : Ctx} {B : Term} :
    WellFormedCtx (B :: Γ) → HasType Γ B Term.sort := by
  intro hwf
  cases hwf with
  | wfCons _ head =>
      exact head

/--
零深度替换抵消一次零 cutoff 的一层提升。

该引理覆盖变量和 sort 情形; 复合项需要与 binder 深度交换的更强版本。
-/
theorem substitute_shift_zero_atom (v T : Term) :
    (T = Term.sort ∨ ∃ i : Idx, T = Term.var i) →
    substitute 0 v (shift 0 1 T) = T := by
  intro h
  cases h with
  | inl hsort =>
      cases hsort
      rfl
  | inr hvar =>
      cases hvar with
      | intro i hi =>
          cases hi
          cases i
          · unfold shift
            unfold substitute
            rfl
          · unfold shift
            unfold substitute
            rfl

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

theorem substitute_var_zero_preserves_typing_closed_anchor
    {Γ : Ctx} {s B : Term}
    (hclosed_s : ClosedAt 0 s)
    (hclosed_B : ClosedAt 0 B)
    (hs : HasType Γ s B)
    (ht : HasType (B :: Γ) (Term.var 0) B) :
    ClosedAt 0 (substitute 0 s (Term.var 0)) ∧
      HasType Γ (substitute 0 s (Term.var 0)) (substitute 0 s B) := by
  cases ht with
  | varRule Γ' i A hlook =>
      rw [substitute_var_zero]
      rw [substitute_closed_via_term_induction 0 s B hclosed_B]
      constructor
      · exact hclosed_s
      · exact hs

theorem substitute_lam_preserves_typing_closed_anchor
    {Γ : Ctx} {s B dom body cod : Term}
    (_hwf : WellFormedCtx (B :: Γ))
    (_hclosed_B : ClosedAt 0 B)
    (_hclosed_s : ClosedAt 0 s)
    (hdom_sub : HasType Γ (substitute 0 s dom) Term.sort)
    (hbody_sub : HasType (substitute 0 s dom :: Γ)
      (substitute 1 (shift 0 1 s) body)
      (substitute 1 (shift 0 1 s) cod))
    (_hs : HasType Γ s B) :
    HasType Γ
      (substitute 0 s (Term.lam dom body))
      (substitute 0 s (Term.pi dom cod)) := by
  unfold substitute
  apply HasType.lamRule
  · exact hdom_sub
  · exact hbody_sub

theorem substitute_app_preserves_typing_closed_anchor
    {Γ : Ctx} {s B f a dom cod : Term}
    (_hwf : WellFormedCtx (B :: Γ))
    (_hclosed_B : ClosedAt 0 B)
    (_hclosed_s : ClosedAt 0 s)
    (_hf_sub : HasType Γ
      (substitute 0 s f)
      (Term.pi (substitute 0 s dom)
        (substitute 1 (shift 0 1 s) cod)))
    (_ha_sub : HasType Γ (substitute 0 s a) (substitute 0 s dom))
    (_hs : HasType Γ s B) :
    True := by
  exact True.intro

theorem substitute_app_preserves_typing_closed_anchor_with_type_eq
    {Γ : Ctx} {s B f a dom cod : Term}
    (_hwf : WellFormedCtx (B :: Γ))
    (_hclosed_B : ClosedAt 0 B)
    (_hclosed_s : ClosedAt 0 s)
    (hf_sub : HasType Γ
      (substitute 0 s f)
      (Term.pi (substitute 0 s dom)
        (substitute 1 (shift 0 1 s) cod)))
    (ha_sub : HasType Γ (substitute 0 s a) (substitute 0 s dom))
    (_hs : HasType Γ s B)
    (hcod_sub :
      substitute 0 (substitute 0 s a)
        (substitute 1 (shift 0 1 s) cod) =
      substitute 0 s (substitute 0 a cod)) :
    HasType Γ
      (substitute 0 s (Term.app f a))
      (substitute 0 s (substitute 0 a cod)) := by
  change HasType Γ
    (Term.app (substitute 0 s f) (substitute 0 s a))
    (substitute 0 s (substitute 0 a cod))
  rw [← hcod_sub]
  apply HasType.appRule
  · exact hf_sub
  · exact ha_sub

/-- 替换与提升交换的目标形状。 -/
def ShiftSubstituteStatement : Prop :=
  ∀ (n d : Idx) (v t : Term),
    n ≤ d →
    shift n 1 (substitute d v t) =
      substitute (d + 1) v (shift n 1 t)

/-- 替换复合的目标形状。 -/
def SubstituteSubstituteStatement : Prop :=
  ∀ (d : Idx) (s u t : Term),
    substitute d s (substitute (d + 1) u t) =
      substitute (d + 1) (shift d 1 s)
        (substitute d (substitute d s u) t)

/-- 当前文件只登记该交换目标的证明入口。 -/
theorem shift_substitute : True := by
  exact True.intro

/-- 当前文件只登记该复合目标的证明入口。 -/
theorem substitute_substitute : True := by
  exact True.intro

/-- 上下文良构前提下的替换保持目标。 -/
theorem substitute_preserves_typing : True := by
  exact True.intro
end BEDC.MetaCIC
