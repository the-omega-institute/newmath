import BEDC.Derived.HolomorphicUp
import BEDC.Derived.ProdUp

namespace BEDC.Derived.ResidueUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp
open BEDC.Derived.HolomorphicUp
open BEDC.Derived.ProdUp

def ResiduePoleData
    (f center radius pole gap integral residue : BHist) : Prop :=
  HolomorphicOpenDisk center radius pole gap ∧ ComplexHistoryCarrier integral ∧
    ComplexHistoryCarrier residue ∧
      ProdHistoryCarrier ComplexHistoryCarrier ComplexHistoryCarrier f ∧
        Cont integral residue f

theorem ResiduePoleData_hsame_transport
    {f f' center center' radius radius' pole pole' gap gap' integral integral'
      residue residue' : BHist} :
    ResiduePoleData f center radius pole gap integral residue -> hsame f f' ->
      hsame center center' -> hsame radius radius' -> hsame pole pole' -> hsame gap gap' ->
        hsame integral integral' -> hsame residue residue' ->
          ResiduePoleData f' center' radius' pole' gap' integral' residue' ∧
            Cont integral' residue' f' := by
  intro data sameF sameCenter sameRadius samePole sameGap sameIntegral sameResidue
  cases data with
  | intro disk rest =>
      cases rest with
      | intro integralCarrier rest =>
          cases rest with
          | intro residueCarrier rest =>
              cases rest with
              | intro productCarrier integralResidue =>
                  have disk' : HolomorphicOpenDisk center' radius' pole' gap' :=
                    (HolomorphicOpenDisk_hsame_transport sameCenter sameRadius samePole sameGap
                      disk).left
                  have integralCarrier' : ComplexHistoryCarrier integral' :=
                    ProdHistoryCarrier_hsame_transport sameIntegral integralCarrier
                  have residueCarrier' : ComplexHistoryCarrier residue' :=
                    ProdHistoryCarrier_hsame_transport sameResidue residueCarrier
                  have productCarrier' :
                      ProdHistoryCarrier ComplexHistoryCarrier ComplexHistoryCarrier f' :=
                    ProdHistoryCarrier_hsame_transport sameF productCarrier
                  have integralResidue' : Cont integral' residue' f' :=
                    cont_hsame_transport sameIntegral sameResidue sameF integralResidue
                  exact And.intro
                    (And.intro disk'
                      (And.intro integralCarrier'
                        (And.intro residueCarrier'
                          (And.intro productCarrier' integralResidue'))))
                    integralResidue'

theorem ResiduePoleData_result_determinism
    {f f' center radius pole gap integral residue : BHist} :
    ResiduePoleData f center radius pole gap integral residue ->
      ResiduePoleData f' center radius pole gap integral residue ->
        hsame f f' ∧ Cont integral residue f ∧ Cont integral residue f' := by
  intro leftData rightData
  cases leftData with
  | intro _leftDisk leftRest =>
      cases leftRest with
      | intro _leftIntegralCarrier leftRest =>
          cases leftRest with
          | intro _leftResidueCarrier leftRest =>
              cases leftRest with
              | intro _leftProductCarrier leftCont =>
                  cases rightData with
                  | intro _rightDisk rightRest =>
                      cases rightRest with
                      | intro _rightIntegralCarrier rightRest =>
                          cases rightRest with
                          | intro _rightResidueCarrier rightRest =>
                              cases rightRest with
                              | intro _rightProductCarrier rightCont =>
                                  exact And.intro
                                    (cont_deterministic leftCont rightCont)
                                    (And.intro leftCont rightCont)

theorem ResiduePoleData_empty_function_endpoints
    {f center radius pole gap integral residue : BHist} :
    ResiduePoleData f center radius pole gap integral residue -> hsame f BHist.Empty ->
      hsame integral BHist.Empty ∧ hsame residue BHist.Empty := by
  intro data functionEmpty
  cases data with
  | intro _disk rest =>
      cases rest with
      | intro _integralCarrier rest =>
          cases rest with
          | intro _residueCarrier rest =>
              cases rest with
              | intro _productCarrier integralResidue =>
                  have emptyContinuation : Cont integral residue BHist.Empty :=
                    cont_result_hsame_transport integralResidue functionEmpty
                  exact cont_empty_result_inversion emptyContinuation

theorem ResiduePoleData_empty_function_endpoints_iff
    {f center radius pole gap integral residue : BHist} :
    ResiduePoleData f center radius pole gap integral residue ->
      (hsame f BHist.Empty ↔
        hsame integral BHist.Empty ∧ hsame residue BHist.Empty) := by
  intro data
  constructor
  · intro functionEmpty
    exact ResiduePoleData_empty_function_endpoints data functionEmpty
  · intro endpoints
    cases data with
    | intro _disk rest =>
        cases rest with
        | intro _integralCarrier rest =>
            cases rest with
            | intro _residueCarrier rest =>
                cases rest with
                | intro _productCarrier integralResidue =>
                    exact
                      cont_respects_hsame endpoints.left endpoints.right integralResidue
                        (cont_intro rfl)

theorem ResiduePoleData_residue_suffix_closure
    {f center radius pole gap integral residue q fq : BHist} :
    ResiduePoleData f center radius pole gap integral residue -> UnaryHistory q ->
      Cont f q fq ->
        ∃ residueq : BHist,
          ResiduePoleData fq center radius pole gap integral residueq ∧
            Cont residue q residueq ∧ Cont integral residueq fq := by
  intro data suffixCarrier functionSuffix
  cases data with
  | intro disk rest =>
      cases rest with
      | intro integralCarrier rest =>
          cases rest with
          | intro residueCarrier rest =>
              cases rest with
              | intro _productCarrier integralResidue =>
                  have residueSuffixData :=
                    cont_assoc_middle_exists integralResidue functionSuffix
                  cases residueSuffixData with
                  | intro residueq residueqData =>
                      cases residueqData with
                      | intro residueSuffix integralResidueq =>
                          have residueqCarrier : ComplexHistoryCarrier residueq := by
                            cases residueSuffix
                            exact
                              ComplexHistoryCarrier_append_unary_closed residueCarrier
                                suffixCarrier
                          have productCarrier :
                              ProdHistoryCarrier ComplexHistoryCarrier ComplexHistoryCarrier fq :=
                            ProdHistoryCarrier_cont_intro integralCarrier residueqCarrier
                              integralResidueq
                          exact Exists.intro residueq
                            (And.intro
                              (And.intro disk
                                (And.intro integralCarrier
                                  (And.intro residueqCarrier
                                    (And.intro productCarrier integralResidueq))))
                              (And.intro residueSuffix integralResidueq))

theorem ResiduePoleData_suffix_closure_empty_function_endpoints
    {f center radius pole gap integral residue q fq : BHist} :
    ResiduePoleData f center radius pole gap integral residue -> UnaryHistory q -> Cont f q fq ->
      hsame fq BHist.Empty ->
        exists residueq : BHist,
          ResiduePoleData fq center radius pole gap integral residueq ∧
            Cont residue q residueq ∧ hsame integral BHist.Empty ∧
              hsame residueq BHist.Empty := by
  intro data suffixCarrier functionSuffix functionEmpty
  have closed :=
    ResiduePoleData_residue_suffix_closure data suffixCarrier functionSuffix
  cases closed with
  | intro residueq closedData =>
      have endpoints :=
        ResiduePoleData_empty_function_endpoints closedData.left functionEmpty
      exact Exists.intro residueq
        (And.intro closedData.left
          (And.intro closedData.right.left
            (And.intro endpoints.left endpoints.right)))

theorem ResiduePoleData_empty_suffix_reflects_endpoints
    {f center radius pole gap integral residue q fq : BHist} :
    ResiduePoleData f center radius pole gap integral residue -> Cont f q fq ->
      hsame fq BHist.Empty ->
        hsame integral BHist.Empty ∧ hsame residue BHist.Empty ∧ hsame q BHist.Empty := by
  intro data suffix resultEmpty
  have emptyContinuation : Cont f q BHist.Empty :=
    cont_result_hsame_transport suffix resultEmpty
  have endpoints := cont_empty_result_inversion emptyContinuation
  have functionEndpoints :=
    ResiduePoleData_empty_function_endpoints data endpoints.left
  exact And.intro functionEndpoints.left
    (And.intro functionEndpoints.right endpoints.right)

theorem ResiduePoleData_prefix_empty_reflects_endpoints
    {f center radius pole gap integral residue q qf : BHist} :
    ResiduePoleData f center radius pole gap integral residue -> Cont q f qf ->
      hsame qf BHist.Empty ->
        hsame q BHist.Empty ∧ hsame integral BHist.Empty ∧ hsame residue BHist.Empty := by
  intro data prefixCont resultEmpty
  have emptyContinuation : Cont q f BHist.Empty :=
    cont_result_hsame_transport prefixCont resultEmpty
  have endpoints := cont_empty_result_inversion emptyContinuation
  have functionEndpoints :=
    ResiduePoleData_empty_function_endpoints data endpoints.right
  exact And.intro endpoints.left
    (And.intro functionEndpoints.left functionEndpoints.right)

theorem ResiduePoleData_suffix_empty_function_endpoints
    {f center radius pole gap integral residue q fq : BHist} :
    ResiduePoleData f center radius pole gap integral residue -> UnaryHistory q ->
      Cont f q fq -> hsame fq BHist.Empty ->
        hsame integral BHist.Empty ∧
          ∃ residueq : BHist, Cont residue q residueq ∧ hsame residueq BHist.Empty := by
  intro data suffixCarrier functionSuffix functionSuffixEmpty
  have suffixClosure :=
    ResiduePoleData_residue_suffix_closure data suffixCarrier functionSuffix
  cases suffixClosure with
  | intro residueq residueqData =>
      cases residueqData with
      | intro shiftedData residueqWitness =>
          have shiftedEndpoints :=
            ResiduePoleData_empty_function_endpoints shiftedData functionSuffixEmpty
          exact And.intro shiftedEndpoints.left
            (Exists.intro residueq
              (And.intro residueqWitness.left shiftedEndpoints.right))

theorem ResiduePoleData_integral_prefix_closure
    {f center radius pole gap integral residue q qf : BHist} :
    ResiduePoleData f center radius pole gap integral residue -> UnaryHistory q ->
      Cont q f qf ->
        ∃ integralq : BHist,
          ResiduePoleData qf center radius pole gap integralq residue ∧
            Cont q integral integralq ∧ Cont integralq residue qf := by
  intro data prefixCarrier functionPrefix
  cases data with
  | intro disk rest =>
      cases rest with
      | intro integralCarrier rest =>
          cases rest with
          | intro residueCarrier rest =>
              cases rest with
              | intro _productCarrier integralResidue =>
                  let integralq := append q integral
                  have integralqCarrier : ComplexHistoryCarrier integralq :=
                    ComplexHistoryCarrier_prepend_unary_closed prefixCarrier integralCarrier
                  have prefixIntegral : Cont q integral integralq :=
                    cont_intro rfl
                  have integralqResidue : Cont integralq residue qf := by
                    cases functionPrefix
                    cases integralResidue
                    exact cont_intro (append_assoc q integral residue).symm
                  have productCarrier :
                      ProdHistoryCarrier ComplexHistoryCarrier ComplexHistoryCarrier qf :=
                    ProdHistoryCarrier_cont_intro integralqCarrier residueCarrier
                      integralqResidue
                  exact Exists.intro integralq
                    (And.intro
                      (And.intro disk
                        (And.intro integralqCarrier
                          (And.intro residueCarrier
                            (And.intro productCarrier integralqResidue))))
                      (And.intro prefixIntegral integralqResidue))

theorem ResiduePoleData_integral_suffix_closure
    {f center radius pole gap integral residue q fq : BHist} :
    ResiduePoleData f center radius pole gap integral residue -> UnaryHistory q -> Cont f q fq ->
      exists integralq : BHist, ResiduePoleData fq center radius pole gap integralq residue ∧
        Cont integral q integralq ∧ Cont integralq residue fq := by
  intro data suffixCarrier functionSuffix
  cases data with
  | intro disk rest =>
      cases rest with
      | intro integralCarrier rest =>
          cases rest with
          | intro residueCarrier rest =>
              cases rest with
              | intro _productCarrier integralResidue =>
                  let integralq := append integral q
                  have integralqCarrier : ComplexHistoryCarrier integralq :=
                    ComplexHistoryCarrier_append_unary_closed integralCarrier suffixCarrier
                  have integralSuffix : Cont integral q integralq :=
                    cont_intro rfl
                  have residueUnary : UnaryHistory residue :=
                    ComplexHistoryCarrier_unary residueCarrier
                  have integralqResidueCanonical :
                      Cont integralq residue (append integralq residue) :=
                    cont_intro rfl
                  have sameCanonicalFq : hsame (append integralq residue) fq := by
                    have sameSwap : hsame (append q residue) (append residue q) :=
                      unary_append_comm suffixCarrier residueUnary
                    have sameNested :
                        hsame (append integral (append q residue))
                          (append integral (append residue q)) :=
                      congrArg (append integral) sameSwap
                    exact hsame_trans
                      (append_assoc integral q residue)
                        (hsame_trans sameNested
                          (hsame_trans
                            (hsame_symm (append_assoc integral residue q))
                          (hsame_trans
                            (hsame_symm (congrArg (fun visible => append visible q) integralResidue))
                            (hsame_symm functionSuffix))))
                  have integralqResidue : Cont integralq residue fq :=
                    cont_result_hsame_transport integralqResidueCanonical sameCanonicalFq
                  have productCarrier :
                      ProdHistoryCarrier ComplexHistoryCarrier ComplexHistoryCarrier fq :=
                    ProdHistoryCarrier_cont_intro integralqCarrier residueCarrier
                      integralqResidue
                  exact Exists.intro integralq
                    (And.intro
                      (And.intro disk
                        (And.intro integralqCarrier
                          (And.intro residueCarrier
                            (And.intro productCarrier integralqResidue))))
                      (And.intro integralSuffix integralqResidue))

theorem ResiduePoleData_integral_prefix_empty_function_endpoints
    {f center radius pole gap integral residue q qf : BHist} :
    ResiduePoleData f center radius pole gap integral residue -> UnaryHistory q ->
      Cont q f qf -> hsame qf BHist.Empty ->
        exists integralq : BHist,
          ResiduePoleData qf center radius pole gap integralq residue ∧
            Cont q integral integralq ∧ hsame integralq BHist.Empty ∧
              hsame residue BHist.Empty := by
  intro data prefixCarrier functionPrefix functionEmpty
  have closed :=
    ResiduePoleData_integral_prefix_closure data prefixCarrier functionPrefix
  cases closed with
  | intro integralq closedData =>
      have endpoints :=
        ResiduePoleData_empty_function_endpoints closedData.left functionEmpty
      exact Exists.intro integralq
        (And.intro closedData.left
          (And.intro closedData.right.left
            (And.intro endpoints.left endpoints.right)))

theorem ResiduePoleData_result_determinism_with_continuations
    {f f' center radius pole gap integral residue : BHist} :
    ResiduePoleData f center radius pole gap integral residue ->
      ResiduePoleData f' center radius pole gap integral residue ->
        Cont integral residue f ∧ Cont integral residue f' ∧ hsame f f' := by
  intro leftData rightData
  have leftCont : Cont integral residue f := leftData.right.right.right.right
  have rightCont : Cont integral residue f' := rightData.right.right.right.right
  exact And.intro leftCont (And.intro rightCont (cont_deterministic leftCont rightCont))

end BEDC.Derived.ResidueUp
