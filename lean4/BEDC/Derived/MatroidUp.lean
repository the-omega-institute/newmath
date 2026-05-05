import BEDC.Derived.FinsetUp

namespace BEDC.Derived.MatroidUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.Derived.FinsetUp

def MatroidFinsetEnumerates
    (E : BHist -> Prop) (Rel : BHist -> BHist -> Prop)
    (bundle : ProbeBundle BHist) (J : BHist -> Prop) : Prop :=
  FinsetEnumerationBundle E bundle ∧
    forall z : BHist, J z <-> FinsetEnumerationCarrier E Rel bundle z

def MatroidFinsetSubset
    (E : BHist -> Prop) (Rel : BHist -> BHist -> Prop)
    (J I : BHist -> Prop) : Prop :=
  (exists zs : ProbeBundle BHist, MatroidFinsetEnumerates E Rel zs J) ∧
    forall z : BHist, J z -> I z

def MatroidFinsetIntersection
    (E : BHist -> Prop) (Rel : BHist -> BHist -> Prop)
    (J I K : BHist -> Prop) : Prop :=
  exists zs : ProbeBundle BHist,
    MatroidFinsetEnumerates E Rel zs J ∧ forall z : BHist, J z <-> I z ∧ K z

theorem MatroidFinsetIntersection_left_subset
    {E : BHist -> Prop} {Rel : BHist -> BHist -> Prop} {I K J : BHist -> Prop} :
    MatroidFinsetIntersection E Rel J I K ->
      MatroidFinsetSubset E Rel J I ∧
        exists zs : ProbeBundle BHist, MatroidFinsetEnumerates E Rel zs J := by
  intro intersection
  cases intersection with
  | intro zs data =>
      cases data with
      | intro enumerates pointwise =>
          have finiteSpine :
              exists zs : ProbeBundle BHist, MatroidFinsetEnumerates E Rel zs J :=
            Exists.intro zs enumerates
          have subset : MatroidFinsetSubset E Rel J I := by
            constructor
            · exact finiteSpine
            · intro z memberJ
              exact (Iff.mp (pointwise z) memberJ).left
          exact And.intro subset finiteSpine

end BEDC.Derived.MatroidUp
