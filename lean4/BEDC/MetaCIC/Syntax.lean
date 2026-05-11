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

/-- 朴素 substitute: 把 depth 处变量替换为 v；当前层假设 v 是 closed term。 -/
def substitute (depth : Idx) (v : Term) : Term → Term
  | Term.var i => if i = depth then v else Term.var i
  | Term.app f a => Term.app (substitute depth v f) (substitute depth v a)
  | Term.lam d b => Term.lam (substitute depth v d) (substitute (depth + 1) v b)
  | Term.pi d c => Term.pi (substitute depth v d) (substitute (depth + 1) v c)
  | Term.sort => Term.sort

end BEDC.MetaCIC
