import BEDC.Algebra.FiniteFold

namespace BEDC.Algebra.FinPerm

open BEDC.Algebra.Rel
open BEDC.Algebra.FiniteFold

def finRange : (n : Nat) -> List (Fin n)
  | 0 => []
  | Nat.succ n => ⟨0, Nat.zero_lt_succ n⟩ ::
      List.map (fun i : Fin n => ⟨Nat.succ i.val, Nat.succ_lt_succ i.isLt⟩) (finRange n)

structure FinPerm (n : Nat) where
  data : List (Fin n)
  permutes : ListPerm data (finRange n)

def FinPerm.identity (n : Nat) : FinPerm n :=
  { data := finRange n
    permutes := listPerm_refl (finRange n) }

def applyPerm {A : Type u} {n : Nat} (p : FinPerm n) (xs : List A) (fallback : A) : List A :=
  List.map (fun i : Fin n => List.getD xs i.val fallback) p.data

def permutedValues {A : Type u} {n : Nat} (p : FinPerm n) (f : Fin n -> A) : List A :=
  List.map f p.data

theorem finPerm_data_permutes {n : Nat} (p : FinPerm n) :
    ListPerm p.data (finRange n) :=
  p.permutes

theorem finPerm_values_permutes {A : Type u} {n : Nat} (p : FinPerm n) (f : Fin n -> A) :
    ListPerm (permutedValues p f) (List.map f (finRange n)) := by
  exact listPerm_map f p.permutes

theorem listProd_finPermInvariant {A : Type u} {r : A -> A -> Prop}
    (R : RelCommRing A r) {n : Nat} (p : FinPerm n) (f : Fin n -> A) :
    r (listProd R (permutedValues p f)) (listProd R (List.map f (finRange n))) :=
  prod_permInvariant R (finPerm_values_permutes p f)

theorem listSum_finPermInvariant {A : Type u} {r : A -> A -> Prop}
    (R : RelCommRing A r) {n : Nat} (p : FinPerm n) (f : Fin n -> A) :
    r (listSum R (permutedValues p f)) (listSum R (List.map f (finRange n))) :=
  sum_permInvariant R (finPerm_values_permutes p f)

end BEDC.Algebra.FinPerm
