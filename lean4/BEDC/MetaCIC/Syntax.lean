import BEDC.FKernel.Mark

namespace BEDC.MetaCIC

/-- de Bruijn indices. BHist-based encoding 是理想形态；V1 先用 Lean 内置 Nat。 -/
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
  | Term.var i => if i ≥ cutoff then Term.var (i + amount) else Term.var i
  | Term.app f a => Term.app (shift cutoff amount f) (shift cutoff amount a)
  | Term.lam d b => Term.lam (shift cutoff amount d) (shift (cutoff + 1) amount b)
  | Term.pi d c => Term.pi (shift cutoff amount d) (shift (cutoff + 1) amount c)
  | Term.sort => Term.sort

/-- Substitute `v` for `var depth`, shifting `v` when descending under binders. -/
def substitute (depth : Idx) (v : Term) : Term → Term
  | Term.var i =>
      if i = depth then v else if i > depth then Term.var (i - 1) else Term.var i
  | Term.app f a => Term.app (substitute depth v f) (substitute depth v a)
  | Term.lam d b => Term.lam (substitute depth v d) (substitute (depth + 1) (shift 0 1 v) b)
  | Term.pi d c => Term.pi (substitute depth v d) (substitute (depth + 1) (shift 0 1 v) c)
  | Term.sort => Term.sort

end BEDC.MetaCIC
