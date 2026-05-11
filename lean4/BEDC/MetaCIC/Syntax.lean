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

end BEDC.MetaCIC
