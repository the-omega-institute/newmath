import BEDC.FKernel.Mark

namespace BEDC.MetaCIC

/-- de Bruijn indices。BHist-based encoding 是理想形态；当前以 Lean 内置 Nat 编码。 -/
abbrev Idx := Nat

/-- 极简 MetaCIC term: 变量、应用、lambda、Pi、单一宇宙。 -/
inductive Term : Type where
  | var (i : Idx)
  | app (f a : Term)
  | lam (dom body : Term)
  | pi (dom cod : Term)
  | sort

/-- `shift cutoff amount t` shifts free variables at or above `cutoff` by `amount`. -/
def shift (cutoff amount : Idx) : Term → Term
  | Term.var i =>
      match Nat.ble cutoff i with
      | true => Term.var (i + amount)
      | false => Term.var i
  | Term.app f a => Term.app (shift cutoff amount f) (shift cutoff amount a)
  | Term.lam d b => Term.lam (shift cutoff amount d) (shift (cutoff + 1) amount b)
  | Term.pi d c => Term.pi (shift cutoff amount d) (shift (cutoff + 1) amount c)
  | Term.sort => Term.sort

/-- Substitute `v` for `var depth`, shifting `v` when descending under binders. -/
def substitute (depth : Idx) (v : Term) : Term → Term
  | Term.var i =>
      match Nat.beq i depth, Nat.blt depth i with
      | true, _ => v
      | false, true => Term.var (i - 1)
      | false, false => Term.var i
  | Term.app f a => Term.app (substitute depth v f) (substitute depth v a)
  | Term.lam d b => Term.lam (substitute depth v d) (substitute (depth + 1) (shift 0 1 v) b)
  | Term.pi d c => Term.pi (substitute depth v d) (substitute (depth + 1) (shift 0 1 v) c)
  | Term.sort => Term.sort

/-- Typing context = 类型栈。 -/
abbrev Ctx := List Term

/-- 在 ctx 里 lookup 第 i 个变量的类型；穿过 binder 时同步提升类型。 -/
def Ctx.lookup : Ctx → Idx → Option Term
  | [], _ => none
  | (t :: _), 0 => some t
  | (_ :: rest), n + 1 =>
      match Ctx.lookup rest n with
      | some T => some (shift 0 1 T)
      | none => none

end BEDC.MetaCIC
