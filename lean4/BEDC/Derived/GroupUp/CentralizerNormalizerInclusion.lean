import BEDC.Derived.GroupUp.NormalizerSubgroup

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist

protected theorem group_centralizer_normal_in_normalizer_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a s t x : BHist} :
    let Centralizer := fun y : BHist => hsame (mul y a) (mul a y)
    let Conj := fun u y : BHist => mul (mul u y) (inv u)
    let Normalizer := fun u : BHist =>
      (forall y : BHist, Centralizer y -> Centralizer (Conj u y)) ∧
        (forall y : BHist, Centralizer y -> Centralizer (Conj (inv u) y))
    (Centralizer s -> Normalizer s) ∧
      (Normalizer s -> Centralizer x -> Centralizer (Conj s x) ∧
        Centralizer (Conj (inv s) x)) ∧
      (Normalizer s -> hsame s t -> Normalizer t) := by
  dsimp
  have subgroupRows :=
    BEDC.Derived.GroupUp.group_centralizer_normalizer_subgroup_from_empty_unit
      (mul := mul) (inv := inv) assocC leftId rightId mulCongr leftInv rightInv (a := a)
  dsimp at subgroupRows
  exact And.intro
    (fun centralS => subgroupRows.right.right.right.right centralS)
    (And.intro
      (fun normalizesS centralX =>
        And.intro (normalizesS.left x centralX) (normalizesS.right x centralX))
      (fun normalizesS sameST => subgroupRows.right.right.right.left normalizesS sameST))

end BEDC.Derived.GroupUp
