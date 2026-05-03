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

theorem ComplexDistance_empty_left_iff {w d : BHist} :
    ComplexDistance BHist.Empty w d <-> UnaryHistory w ∧ hsame d w := by
  constructor
  · intro distance
    have same : hsame d w :=
      Or.elim distance.right.right.right
        (fun left => cont_left_unit_result left)
        (fun right => Iff.mp cont_right_unit_iff right)
    exact And.intro distance.right.left same
  · intro data
    have dUnary : UnaryHistory d :=
      unary_transport data.left (hsame_symm data.right)
    have leftContinuation : Cont BHist.Empty w d :=
      Iff.mpr cont_left_unit_iff data.right
    exact And.intro unary_empty
      (And.intro data.left (And.intro dUnary (Or.inl leftContinuation)))

theorem ComplexDistance_hsame_transport_with_relation {z z' w w' d d' : BHist} :
    hsame z z' -> hsame w w' -> hsame d d' -> ComplexDistance z w d ->
      ComplexDistance z' w' d' ∧ (Cont z' w' d' ∨ Cont w' z' d') := by
  intro sameZ sameW sameD distance
  have zUnary : UnaryHistory z' := unary_transport distance.left sameZ
  have wUnary : UnaryHistory w' := unary_transport distance.right.left sameW
  have dUnary : UnaryHistory d' := unary_transport distance.right.right.left sameD
  have relation : Cont z' w' d' ∨ Cont w' z' d' :=
    Or.elim distance.right.right.right
      (fun left => by
        cases sameZ
        cases sameW
        exact Or.inl (cont_result_hsame_transport left sameD))
      (fun right => by
        cases sameZ
        cases sameW
        exact Or.inr (cont_result_hsame_transport right sameD))
  exact And.intro (And.intro zUnary (And.intro wUnary (And.intro dUnary relation))) relation

theorem ComplexDistance_empty_iff {z w : BHist} :
    ComplexDistance z w BHist.Empty ↔
      UnaryHistory z ∧ UnaryHistory w ∧ hsame z BHist.Empty ∧ hsame w BHist.Empty := by
  constructor
  · intro distance
    cases distance.right.right.right with
    | inl zw =>
        have endpoints := cont_empty_result_inversion zw
        exact And.intro distance.left
          (And.intro distance.right.left (And.intro endpoints.left endpoints.right))
    | inr wz =>
        have endpoints := cont_empty_result_inversion wz
        exact And.intro distance.left
          (And.intro distance.right.left (And.intro endpoints.right endpoints.left))
  · intro endpoints
    cases endpoints.right.right.left
    cases endpoints.right.right.right
    exact And.intro endpoints.left
      (And.intro endpoints.right.left
        (And.intro unary_empty (Or.inl (cont_left_unit BHist.Empty))))

theorem ComplexDistance_empty_left_endpoint_iff {w d : BHist} :
    ComplexDistance BHist.Empty w d ↔ UnaryHistory w ∧ hsame d w := by
  constructor
  · intro distance
    cases distance.right.right.right with
    | inl ew =>
        exact And.intro distance.right.left (cont_left_unit_result ew)
    | inr we =>
        exact And.intro distance.right.left (cont_right_unit_iff.mp we)
  · intro data
    cases data.right
    exact And.intro unary_empty
      (And.intro data.left
        (And.intro data.left (Or.inl (cont_left_unit w))))

theorem ComplexDistance_empty_endpoint_iff {z w : BHist} :
    ComplexDistance z w BHist.Empty ↔
      UnaryHistory z ∧ UnaryHistory w ∧ hsame z BHist.Empty ∧ hsame w BHist.Empty :=
  ComplexDistance_empty_iff

end BEDC.Derived.ComplexLimitUp
