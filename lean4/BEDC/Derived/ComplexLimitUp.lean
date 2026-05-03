import BEDC.FKernel.Unary

namespace BEDC.Derived.ComplexLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def ComplexDistance (z w d : BHist) : Prop :=
  UnaryHistory z ∧ UnaryHistory w ∧ UnaryHistory d ∧ (Cont z w d ∨ Cont w z d)

theorem ComplexDistance_symm_iff {z w d : BHist} :
    (ComplexDistance z w d ↔ ComplexDistance w z d) ∧
      (ComplexDistance z w d -> UnaryHistory z ∧ UnaryHistory w ∧ UnaryHistory d) := by
  constructor
  · constructor
    · intro distance
      cases distance with
      | intro zCarrier rest =>
          cases rest with
          | intro wCarrier rest =>
              cases rest with
              | intro dCarrier rel =>
                  exact
                    And.intro wCarrier
                      (And.intro zCarrier
                        (And.intro dCarrier
                          (Or.elim rel
                            (fun zw => Or.inr zw)
                            (fun wz => Or.inl wz))))
    · intro distance
      cases distance with
      | intro wCarrier rest =>
          cases rest with
          | intro zCarrier rest =>
              cases rest with
              | intro dCarrier rel =>
                  exact
                    And.intro zCarrier
                      (And.intro wCarrier
                        (And.intro dCarrier
                          (Or.elim rel
                            (fun wz => Or.inr wz)
                            (fun zw => Or.inl zw))))
  · intro distance
    exact And.intro distance.left (And.intro distance.right.left distance.right.right.left)

end BEDC.Derived.ComplexLimitUp
