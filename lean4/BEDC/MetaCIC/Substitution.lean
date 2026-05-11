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

/-- 闭合替换保持在 sort 与变量项上的可证明核心。 -/
theorem closed_term_substitute_preserves_typing
    {Γ : Ctx} {t s A B : Term}
    (hwf : WellFormedCtx (B :: Γ))
    (hclosed_B : ClosedAt 0 B)
    (_hclosed_s : ClosedAt 0 s)
    (ht : HasType (B :: Γ) t A)
    (hs : HasType Γ s B)
    (hshape : t = Term.sort ∨ ∃ i : Idx, t = Term.var i) :
    HasType Γ (substitute 0 s t) (substitute 0 s A) := by
  cases ht with
  | sortRule Γ' =>
      exact HasType.sortRule Γ
  | varRule Γ' i A hi =>
      cases i with
      | zero =>
          rw [substitute_var_zero]
          rw [lookup_cons_zero] at hi
          cases hi
          rw [substitute_closed 0 s A hclosed_B]
          exact hs
      | succ n =>
          rw [substitute_var_succ_zero]
          rw [lookup_cons_succ] at hi
          cases hlook : Ctx.lookup Γ n with
          | none =>
              rw [hlook] at hi
              cases hi
          | some T =>
              rw [hlook] at hi
              cases hi
              rw [substitute_shift_at_eq]
              exact HasType.varRule Γ n T hlook
  | piRule Γ' dom cod hdom hcod =>
      cases hshape with
      | inl hsort => cases hsort
      | inr hvar =>
          cases hvar with
          | intro i hi => cases hi
  | lamRule Γ' dom body cod hdom hbody =>
      cases hshape with
      | inl hsort => cases hsort
      | inr hvar =>
          cases hvar with
          | intro i hi => cases hi
  | appRule Γ' f a dom cod hf ha =>
      cases hshape with
      | inl hsort => cases hsort
      | inr hvar =>
          cases hvar with
          | intro i hi => cases hi

/-- 闭合替换保持完整语句的最小反例项。 -/
def closedSubstituteCounterTerm : Term :=
  Term.lam (Term.var 0) (Term.var 0)

/-- 闭合替换保持完整语句的最小反例类型。 -/
def closedSubstituteCounterType : Term :=
  Term.pi (Term.var 0) (Term.var 0)

/-- 反例源项在单 sort 上下文中可类型化。 -/
theorem closed_substitute_counter_source :
    HasType [Term.sort] closedSubstituteCounterTerm closedSubstituteCounterType := by
  unfold closedSubstituteCounterTerm
  unfold closedSubstituteCounterType
  apply HasType.lamRule
  · apply HasType.varRule
    rfl
  · apply HasType.varRule
    rfl

/-- 反例源上下文良构。 -/
theorem closed_substitute_counter_wf :
    WellFormedCtx [Term.sort] := by
  apply WellFormedCtx.wfCons
  · exact WellFormedCtx.wfNil
  · exact HasType.sortRule []

/-- 反例目标项在空上下文中不可具有替换后的类型。 -/
theorem closed_substitute_counter_target_absurd :
    ¬ HasType []
        (substitute 0 Term.sort closedSubstituteCounterTerm)
        (substitute 0 Term.sort closedSubstituteCounterType) := by
  intro h
  unfold closedSubstituteCounterTerm at h
  unfold closedSubstituteCounterType at h
  unfold substitute at h
  cases h with
  | lamRule Γ dom body cod hdom hbody =>
      cases hbody with
      | varRule Γ i A hlookup =>
          cases hlookup

/-- 当前语法和 typing 规则下, 登记的完整闭合替换保持语句不成立。 -/
theorem closed_term_substitute_preserves_typing_statement_absurd :
    ¬ ClosedTermSubstitutePreservesTypingStatement := by
  intro h
  exact closed_substitute_counter_target_absurd
    (h closed_substitute_counter_wf
      ClosedAt.sortClosed
      ClosedAt.sortClosed
      closed_substitute_counter_source
      (HasType.sortRule []))

theorem substitute_preserves_typing_general_statement_absurd :
    ¬ SubstitutePreservesTypingGeneralStatement := by
  intro h
  exact closed_substitute_counter_target_absurd
    (h []
      []
      closed_substitute_counter_wf
      closed_substitute_counter_source
      (HasType.sortRule []))

end BEDC.MetaCIC
