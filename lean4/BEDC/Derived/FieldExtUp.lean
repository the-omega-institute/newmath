import BEDC.Derived.FieldUp
import BEDC.Derived.VecSpaceUp

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.Derived.FieldUp
open BEDC.Derived.VecSpaceUp

theorem FieldExtSingletonCarrier_coincidence {h : BHist} :
    FieldSingletonCarrier h ->
      FieldSingletonCarrier h ∧ VecSpaceSingletonCarrier h ∧
        FieldSingletonClassifier h BHist.Empty ∧
          VecSpaceSingletonClassifier h BHist.Empty := by
  intro carrier
  have emptyFieldCarrier : FieldSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyVecCarrier : VecSpaceSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have vecCarrier : VecSpaceSingletonCarrier h := carrier
  have fieldRow : FieldSingletonClassifier h BHist.Empty :=
    And.intro carrier (And.intro emptyFieldCarrier carrier)
  have vecRow : VecSpaceSingletonClassifier h BHist.Empty :=
    And.intro vecCarrier (And.intro emptyVecCarrier carrier)
  exact And.intro carrier (And.intro vecCarrier (And.intro fieldRow vecRow))

theorem FieldExtSingletonOperation_readback_exactness {r m : BHist} :
    FieldSingletonCarrier r -> VecSpaceSingletonCarrier m ->
      FieldSingletonClassifier FieldSingletonZero BHist.Empty ∧
        FieldSingletonClassifier FieldSingletonOne BHist.Empty ∧
          FieldSingletonClassifier (FieldSingletonAdd r m) BHist.Empty ∧
            FieldSingletonClassifier (FieldSingletonNeg r) BHist.Empty ∧
              FieldSingletonClassifier (FieldSingletonMul r m) BHist.Empty ∧
                VecSpaceSingletonClassifier (VecSpaceSingletonSmul r m) BHist.Empty ∧
                  FieldSingletonClassifier (FieldSingletonMul r m)
                    (VecSpaceSingletonSmul r m) := by
  intro _carrierR _carrierM
  have emptyFieldCarrier : FieldSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyVecCarrier : VecSpaceSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have fieldEmptyRow : FieldSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyFieldCarrier
      (And.intro emptyFieldCarrier (hsame_refl BHist.Empty))
  have vecEmptyRow : VecSpaceSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyVecCarrier
      (And.intro emptyVecCarrier (hsame_refl BHist.Empty))
  exact And.intro fieldEmptyRow
    (And.intro fieldEmptyRow
      (And.intro fieldEmptyRow
        (And.intro fieldEmptyRow
          (And.intro fieldEmptyRow
            (And.intro vecEmptyRow fieldEmptyRow)))))

end BEDC.Derived.FieldExtUp
