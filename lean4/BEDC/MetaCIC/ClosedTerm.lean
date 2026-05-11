import BEDC.MetaCIC.Syntax

namespace BEDC.MetaCIC

/-- `ClosedAt n t` 表示 `t` 的所有自由变量都小于 `n`。 -/
inductive ClosedAt : Idx → Term → Prop
  | varClosed {n : Idx} {i : Idx} :
      i < n → ClosedAt n (Term.var i)
  | appClosed {n : Idx} {f a : Term} :
      ClosedAt n f → ClosedAt n a → ClosedAt n (Term.app f a)
  | lamClosed {n : Idx} {dom body : Term} :
      ClosedAt n dom → ClosedAt (n + 1) body → ClosedAt n (Term.lam dom body)
  | piClosed {n : Idx} {dom cod : Term} :
      ClosedAt n dom → ClosedAt (n + 1) cod → ClosedAt n (Term.pi dom cod)
  | sortClosed {n : Idx} :
      ClosedAt n Term.sort

theorem nat_ble_false_of_lt (i n : Nat) :
    i < n → Nat.ble n i = false := by
  induction n generalizing i with
  | zero =>
      intro h
      exact False.elim (Nat.not_lt_zero i h)
  | succ n ih =>
      intro h
      cases i with
      | zero => rfl
      | succ i =>
          exact ih i (Nat.lt_of_succ_lt_succ h)

theorem nat_beq_false_of_lt (i n : Nat) :
    i < n → Nat.beq i n = false := by
  induction n generalizing i with
  | zero =>
      intro h
      exact False.elim (Nat.not_lt_zero i h)
  | succ n ih =>
      intro h
      cases i with
      | zero => rfl
      | succ i =>
          exact ih i (Nat.lt_of_succ_lt_succ h)

theorem nat_blt_false_of_lt (i n : Nat) :
    i < n → Nat.blt n i = false := by
  induction n generalizing i with
  | zero =>
      intro h
      exact False.elim (Nat.not_lt_zero i h)
  | succ n ih =>
      intro h
      cases i with
      | zero => rfl
      | succ i =>
          exact ih i (Nat.lt_of_succ_lt_succ h)

/-- 闭合项在闭合边界处提升不改变语法。 -/
theorem shift_closed (n : Idx) (t : Term) (h : ClosedAt n t) :
    shift n 1 t = t := by
  induction h with
  | varClosed hlt =>
      unfold shift
      rw [nat_ble_false_of_lt _ _ hlt]
  | appClosed _ _ ihf iha =>
      unfold shift
      rw [ihf, iha]
  | lamClosed _ _ ihdom ihbody =>
      unfold shift
      rw [ihdom, ihbody]
  | piClosed _ _ ihdom ihcod =>
      unfold shift
      rw [ihdom, ihcod]
  | sortClosed =>
      rfl

/-- 闭合项在闭合边界处替换不改变语法。 -/
theorem substitute_closed (d : Idx) (v t : Term) (h : ClosedAt d t) :
    substitute d v t = t := by
  induction h generalizing v with
  | varClosed hlt =>
      unfold substitute
      rw [nat_beq_false_of_lt _ _ hlt]
      rw [nat_blt_false_of_lt _ _ hlt]
  | appClosed _ _ ihf iha =>
      unfold substitute
      rw [ihf, iha]
  | lamClosed _ _ ihdom ihbody =>
      unfold substitute
      rw [ihdom, ihbody]
  | piClosed _ _ ihdom ihcod =>
      unfold substitute
      rw [ihdom, ihcod]
  | sortClosed =>
      rfl

end BEDC.MetaCIC
