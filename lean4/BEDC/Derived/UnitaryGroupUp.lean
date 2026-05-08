import BEDC.Derived.LieGroupUp
import BEDC.Derived.VecSpaceUp

namespace BEDC.Derived.UnitaryGroupUp

open BEDC.Derived.LieGroupUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem UnitaryGroupOperationStability_obligation {h k product invH : BHist} :
    VecSpaceSingletonCarrier h -> VecSpaceSingletonCarrier k -> LieGroupSingletonCarrier h ->
      LieGroupSingletonCarrier k -> Cont h k product ->
        Cont BHist.Empty (LieGroupSingletonInv h) invH ->
          VecSpaceSingletonCarrier product ∧ LieGroupSingletonCarrier product ∧
            LieGroupSingletonCarrier invH ∧ hsame product BHist.Empty ∧
              hsame invH BHist.Empty := by
  intro vecH vecK lieH lieK productRow inverseRow
  have productVec : VecSpaceSingletonCarrier product :=
    productRow.trans (append_eq_empty_iff.mpr (And.intro vecH vecK))
  have productLie : LieGroupSingletonCarrier product :=
    productRow.trans (append_eq_empty_iff.mpr (And.intro lieH lieK))
  have inverseEmpty : hsame invH BHist.Empty :=
    cont_left_unit_result inverseRow
  exact And.intro productVec
    (And.intro productLie
      (And.intro inverseEmpty (And.intro productLie inverseEmpty)))

end BEDC.Derived.UnitaryGroupUp
