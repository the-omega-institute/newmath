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

end BEDC.Derived.ResidueUp
