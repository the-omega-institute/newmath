import BEDC.Derived.FinsetUp

namespace BEDC.Derived.MatroidUp

open BEDC.Derived.FinsetUp
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist

def MatroidFinSetSubset (E J I : BHist -> Prop) : Prop :=
  (exists xs : ProbeBundle BHist, FinsetEnumerationBundle E xs ∧
    forall z : BHist, J z <-> FinsetEnumerationCarrier E hsame xs z) ∧
    forall z : BHist, J z -> I z

def MatroidFinSetIntersection (E J I K : BHist -> Prop) : Prop :=
  exists xs : ProbeBundle BHist, FinsetEnumerationBundle E xs ∧
    (forall z : BHist, J z <-> FinsetEnumerationCarrier E hsame xs z) ∧
      forall z : BHist, J z <-> I z ∧ K z

theorem MatroidFinSetIntersection_left_subset {E I K J : BHist -> Prop} :
    MatroidFinSetIntersection E J I K -> MatroidFinSetSubset E J I := by
  intro intersection
  cases intersection with
  | intro xs data =>
      cases data with
      | intro spine rest =>
          cases rest with
          | intro enumerates pointwise =>
              constructor
              · exact Exists.intro xs (And.intro spine enumerates)
              · intro z memberJ
                exact (Iff.mp (pointwise z) memberJ).left

end BEDC.Derived.MatroidUp
