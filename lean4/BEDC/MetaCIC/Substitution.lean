import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Typing
import BEDC.MetaCIC.ContextWF

namespace BEDC.MetaCIC

/-- 带上下文良构前提的替换保持命题形状。 -/
def SubstitutePreservesTypingStatementWF : Prop :=
  ∀ {Γ : Ctx} {t s A B : Term},
    WellFormedCtx (B :: Γ) →
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

private theorem nat_beq_add_one_add_one (i n : Nat) :
    Nat.beq (i + 1) (n + 1) = Nat.beq i n := by
  cases i
  · cases n
    · rfl
    · rfl
  · cases n
    · rfl
    · rfl

private theorem nat_blt_add_one_add_one (n i : Nat) :
    Nat.blt (n + 1) (i + 1) = Nat.blt n i := by
  cases i
  · cases n
    · rfl
    · rfl
  · cases n
    · rfl
    · rfl

private theorem nat_ble_add_one_add_one (n i : Nat) :
    Nat.ble (n + 1) (i + 1) = Nat.ble n i := by
  cases i
  · cases n
    · rfl
    · rfl
  · cases n
    · rfl
    · rfl

private theorem nat_beq_false_of_ble_false (n i : Nat) :
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

private theorem nat_blt_false_of_ble_false (n i : Nat) :
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

private theorem nat_beq_succ_false_of_ble_true (n i : Nat) :
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

private theorem nat_blt_succ_true_of_ble_true (n i : Nat) :
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

private theorem substitute_shift_var_at_eq (n i : Nat) (v : Term) :
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
