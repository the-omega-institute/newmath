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

end BEDC.Derived.ResidueUp
