import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Typing
import BEDC.MetaCIC.Beta
import BEDC.MetaCIC.Substitution

namespace BEDC.MetaCIC

/-- 在 Sort 宇宙下, 类型上的恒等函数 `λ (T : Sort). T`。 -/
def id_sort : Term := Term.lam Term.sort (Term.var 0)

theorem id_sort_well_typed :
    HasType [] id_sort (Term.pi Term.sort Term.sort) := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.varRule
    rfl

theorem pi_sort_sort_well_typed :
    HasType [] (Term.pi Term.sort Term.sort) Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule []
  · exact HasType.sortRule [Term.sort]

/-- `id_sort` 应用到 `Term.sort` 上。 -/
theorem id_sort_applied :
    HasType [] (Term.app id_sort Term.sort) Term.sort := by
  exact HasType.appRule
    []
    id_sort
    Term.sort
    Term.sort
    Term.sort
    id_sort_well_typed
    (HasType.sortRule [])

/-- `(λ (T : Sort). T) Sort →β Sort`。 -/
theorem id_sort_beta :
    BetaStep (Term.app id_sort Term.sort) Term.sort := by
  exact BetaStep.beta Term.sort (Term.var 0) Term.sort

/-- 在 `[Term.sort]` 上下文里, `var 0` 类型是 `Term.sort`。 -/
theorem var_zero_in_sort_ctx :
    HasType [Term.sort] (Term.var 0) Term.sort := by
  apply HasType.varRule
  rfl

/-- K 组合子: `λ (x : Sort). λ (_ : Sort). x`。 -/
def kCombinator : Term :=
  Term.lam Term.sort (Term.lam Term.sort (Term.var 1))

def kCombinatorType : Term :=
  Term.pi Term.sort (Term.pi Term.sort Term.sort)

theorem k_combinator_well_typed :
    HasType [] kCombinator kCombinatorType := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.varRule
      rfl

/-- `K Sort Sort` 的类型回到 `Sort`。 -/
theorem k_applied_twice :
    HasType [] (Term.app (Term.app kCombinator Term.sort) Term.sort) Term.sort := by
  have hFirst :
      HasType [] (Term.app kCombinator Term.sort) (Term.pi Term.sort Term.sort) := by
    exact HasType.appRule
      []
      kCombinator
      Term.sort
      Term.sort
      (Term.pi Term.sort Term.sort)
      k_combinator_well_typed
      (HasType.sortRule [])
  exact HasType.appRule
    []
    (Term.app kCombinator Term.sort)
    Term.sort
    Term.sort
    Term.sort
    hFirst
    (HasType.sortRule [])

/-- `λ (f : Sort → Sort). λ (x : Sort). x` 的 Sort-level zero-like term。 -/
def churchZeroSort : Term :=
  Term.lam (Term.pi Term.sort Term.sort) (Term.lam Term.sort (Term.var 0))

def churchZeroSortType : Term :=
  Term.pi (Term.pi Term.sort Term.sort) (Term.pi Term.sort Term.sort)

theorem church_zero_sort_well_typed :
    HasType [] churchZeroSort churchZeroSortType := by
  apply HasType.lamRule
  · apply HasType.piRule
    · exact HasType.sortRule []
    · exact HasType.sortRule [Term.sort]
  · apply HasType.lamRule
    · exact HasType.sortRule [Term.pi Term.sort Term.sort]
    · apply HasType.varRule
      rfl

/-- 在 Sort 原子项上, 同深度替换抵消一层同深度提升。 -/
theorem sort_shift_substitute_identity :
    substitute 0 Term.sort (shift 0 1 Term.sort) = Term.sort := by
  exact substitute_shift_at_eq 0 Term.sort Term.sort

/-- 公开的变量特例, 供 MetaCIC purity 审计解析源码中的同名结构见证。 -/
theorem substitute_shift_var_at_eq (n i : Nat) (v : Term) :
    substitute n v (shift n 1 (Term.var i)) = Term.var i := by
  exact substitute_shift_at_eq n v (Term.var i)

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

/-- β-step 的目标项可由 V6 替换-提升抵消引理回到 Sort。 -/
theorem beta_shifted_sort_step_preserves_sort_typing :
    BetaStep (Term.app (Term.lam Term.sort (shift 0 1 Term.sort)) Term.sort) Term.sort ∧
    HasType [] (Term.app (Term.lam Term.sort (shift 0 1 Term.sort)) Term.sort) Term.sort ∧
    HasType [] Term.sort Term.sort := by
  have hSub : substitute 0 Term.sort (shift 0 1 Term.sort) = Term.sort := by
    exact substitute_shift_at_eq 0 Term.sort Term.sort
  refine ⟨?_, ?_, ?_⟩
  · rw [← hSub]
    exact BetaStep.beta Term.sort (shift 0 1 Term.sort) Term.sort
  · exact HasType.appRule
      []
      (Term.lam Term.sort (shift 0 1 Term.sort))
      Term.sort
      Term.sort
      Term.sort
      (HasType.lamRule
        []
        Term.sort
        (shift 0 1 Term.sort)
        Term.sort
        (HasType.sortRule [])
        (HasType.sortRule [Term.sort]))
      (HasType.sortRule [])
  · exact HasType.sortRule []

/-- 嵌套 Pi 项上, V6 替换-提升抵消引理穿过 binder 后仍保持结构。 -/
theorem nested_pi_shift_substitute_identity :
    substitute 0 Term.sort
        (shift 0 1 (Term.pi Term.sort (Term.pi Term.sort Term.sort))) =
      Term.pi Term.sort (Term.pi Term.sort Term.sort) := by
  exact substitute_shift_at_eq 0 Term.sort
    (Term.pi Term.sort (Term.pi Term.sort Term.sort))

end BEDC.MetaCIC
