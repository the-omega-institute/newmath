import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist

namespace BEDC.Derived.MatroidUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist

def MatroidFinSetSpineEnumerates (E : BHist -> Prop) (Rel : BHist -> BHist -> Prop)
    (xs : ProbeBundle BHist) (S : BHist -> Prop) : Prop :=
  (forall x : BHist, InBundle x xs -> E x) ∧
    (forall z : BHist, S z <-> exists x : BHist, InBundle x xs ∧ Rel z x)

def MatroidFinSetIntersection (E : BHist -> Prop) (Rel : BHist -> BHist -> Prop)
    (J I K : BHist -> Prop) : Prop :=
  exists xs : ProbeBundle BHist,
    MatroidFinSetSpineEnumerates E Rel xs J ∧ forall z : BHist, J z <-> I z ∧ K z

theorem MatroidFinSetIntersection_left_subset {E : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} {I K J : BHist -> Prop} :
    MatroidFinSetIntersection E Rel J I K ->
      exists xs : ProbeBundle BHist,
        MatroidFinSetSpineEnumerates E Rel xs J ∧ forall z : BHist, J z -> I z := by
  intro intersection
  cases intersection with
  | intro xs data =>
      exact Exists.intro xs
        (And.intro data.left
          (by
            intro z memberJ
            exact (Iff.mp (data.right z) memberJ).left))

end BEDC.Derived.MatroidUp
