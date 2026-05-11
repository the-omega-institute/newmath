import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Typing
import BEDC.MetaCIC.Substitution

namespace BEDC.MetaCIC

/-- 闭原子 term 的极简 type 推断: sort → some sort, var i → Γ.lookup i. -/
def inferAtom (Γ : Ctx) : Term → Option Term
  | Term.sort => some Term.sort
  | Term.var i => Γ.lookup i
  | _ => none

/-- 推断 sort 时, sort : sort 始终成立。 -/
theorem inferAtom_sort_sound (Γ : Ctx) :
    HasType Γ Term.sort Term.sort := HasType.sortRule Γ

/-- 推断 var 时, 若 Γ.lookup i = some A, 则 var i : A. -/
theorem inferAtom_var_sound
    (Γ : Ctx) (i : Idx) (A : Term)
    (h : Γ.lookup i = some A) :
    HasType Γ (Term.var i) A := HasType.varRule Γ i A h

end BEDC.MetaCIC
