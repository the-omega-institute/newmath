import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.NameCert

namespace BEDC.Derived.UnitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

def UnitHistoryCarrier (h : BHist) : Prop :=
  Cont BHist.Empty h BHist.Empty

def UnitHistoryClassifier (h k : BHist) : Prop :=
  UnitHistoryCarrier h ∧ UnitHistoryCarrier k ∧ hsame h k

theorem UnitHistoryCarrier_empty_iff {h : BHist} :
    UnitHistoryCarrier h ↔ hsame h BHist.Empty := by
  constructor
  · intro carrier
    exact cont_right_unit_unique carrier
  · intro same
    cases same
    exact cont_left_unit BHist.Empty

theorem UnitHistoryCarrier_continuation_suffix_closed {h k r : BHist} :
    UnitHistoryCarrier h -> Cont h k r -> hsame r BHist.Empty -> UnitHistoryCarrier k := by
  intro hCarrier hcont rEmpty
  have hEmpty : hsame h BHist.Empty := UnitHistoryCarrier_empty_iff.mp hCarrier
  exact cont_hsame_transport hEmpty (hsame_refl k) rEmpty hcont

theorem UnitHistoryCarrier_continuation_prefix_closed {h k r : BHist} :
    Cont h k r -> hsame r BHist.Empty -> UnitHistoryCarrier h := by
  intro hcont rEmpty
  have emptyContinuation : Cont h k BHist.Empty :=
    cont_result_hsame_transport hcont rEmpty
  have emptyParts := cont_empty_result_inversion emptyContinuation
  exact UnitHistoryCarrier_empty_iff.mpr emptyParts.left

theorem UnitHistoryClassifier_semanticNameCert :
    SemanticNameCert UnitHistoryCarrier UnitHistoryCarrier UnitHistoryCarrier
      UnitHistoryClassifier := by
  constructor
  · constructor
    · exact Exists.intro BHist.Empty (cont_left_unit BHist.Empty)
    · intro h carrier
      exact And.intro carrier (And.intro carrier (hsame_refl h))
    · intro h k same
      exact And.intro same.right.left
        (And.intro same.left (hsame_symm same.right.right))
    · intro h k r sameHK sameKR
      exact And.intro sameHK.left
        (And.intro sameKR.right.left (hsame_trans sameHK.right.right sameKR.right.right))
    · intro h k same _carrier
      exact same.right.left
  · intro h source
    exact source
  · intro h source
    exact source

theorem UnitHistoryClassifier_empty_endpoints_iff {h k : BHist} :
    UnitHistoryClassifier h k ↔ hsame h BHist.Empty ∧ hsame k BHist.Empty := by
  constructor
  · intro classified
    have hParts := cont_empty_result_inversion classified.left
    have kParts := cont_empty_result_inversion classified.right.left
    exact And.intro hParts.right kParts.right
  · intro endpoints
    cases endpoints with
    | intro hEmpty kEmpty =>
        constructor
        · cases hEmpty
          exact cont_left_unit BHist.Empty
        · constructor
          · cases kEmpty
            exact cont_left_unit BHist.Empty
          · exact hsame_trans hEmpty (hsame_symm kEmpty)

theorem UnitHistoryClassifier_append_split_iff {p q h : BHist} :
    UnitHistoryClassifier (append p q) h ↔
      hsame p BHist.Empty ∧ hsame q BHist.Empty ∧ hsame h BHist.Empty := by
  constructor
  · intro classified
    have endpoints := UnitHistoryClassifier_empty_endpoints_iff.mp classified
    have appendParts := append_eq_empty_iff.mp endpoints.left
    exact And.intro appendParts.left (And.intro appendParts.right endpoints.right)
  · intro split
    have appendEmpty : hsame (append p q) BHist.Empty :=
      append_eq_empty_iff.mpr (And.intro split.left split.right.left)
    exact UnitHistoryClassifier_empty_endpoints_iff.mpr
      (And.intro appendEmpty split.right.right)

theorem UnitHistoryClassifier_visible_endpoint_absurd {p q k : BHist} :
    (UnitHistoryClassifier (BHist.e0 p) k -> False) ∧
      (UnitHistoryClassifier (BHist.e1 p) k -> False) ∧
      (UnitHistoryClassifier k (BHist.e0 q) -> False) ∧
      (UnitHistoryClassifier k (BHist.e1 q) -> False) := by
  constructor
  · intro classified
    exact not_hsame_emp_e0 (cont_left_unit_result classified.left)
  · constructor
    · intro classified
      exact not_hsame_emp_e1 (cont_left_unit_result classified.left)
    · constructor
      · intro classified
        exact not_hsame_emp_e0 (cont_left_unit_result classified.right.left)
      · intro classified
        exact not_hsame_emp_e1 (cont_left_unit_result classified.right.left)

theorem UnitHistoryClassifier_continuation_middle_carrier {left middle right : BHist} :
    UnitHistoryClassifier left right -> Cont left middle right -> UnitHistoryCarrier middle := by
  intro classified continuation
  have endpoints := UnitHistoryClassifier_empty_endpoints_iff.mp classified
  have emptyContinuation := cont_result_hsame_transport continuation endpoints.right
  have emptyParts := cont_empty_result_inversion emptyContinuation
  apply UnitHistoryCarrier_empty_iff.mpr
  cases emptyParts.right
  exact hsame_refl BHist.Empty

end BEDC.Derived.UnitUp
