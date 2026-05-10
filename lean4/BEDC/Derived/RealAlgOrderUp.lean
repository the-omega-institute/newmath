import BEDC.Derived.RealUp.Core

namespace BEDC.Derived.RealAlgOrderUp

open BEDC.FKernel.Hist
open BEDC.Derived.RatUp
open BEDC.Derived.RealUp

theorem RealAlgOrderConstantCarrier_classifier_obligations {d e d' e' : BHist} :
    RatHistoryCarrier d -> RatHistoryClassifier d e -> hsame d d' -> hsame e e' ->
      RealConstantHistoryCarrier (BHist.e1 d') ∧
        RealConstantHistoryCarrier (BHist.e1 e') ∧
          RealConstantHistoryClassifier (BHist.e1 d') (BHist.e1 e') ∧
            RatHistoryClassifier d' e' := by
  intro carrierD classifiedDE sameD sameE
  have classifiedD'E' : RatHistoryClassifier d' e' :=
    RatHistoryClassifier_hsame_transport sameD sameE classifiedDE
  have carrierD' : RatHistoryCarrier d' :=
    RatHistoryCarrier_hsame_transport sameD carrierD
  have carrierE' : RatHistoryCarrier e' := classifiedD'E'.right.left
  have realCarrierD' : RealConstantHistoryCarrier (BHist.e1 d') :=
    RealConstantHistoryCarrier_e1_iff_rat.mpr carrierD'
  have realCarrierE' : RealConstantHistoryCarrier (BHist.e1 e') :=
    RealConstantHistoryCarrier_e1_iff_rat.mpr carrierE'
  have realClassifierD'E' : RealConstantHistoryClassifier (BHist.e1 d') (BHist.e1 e') :=
    RealConstantHistoryClassifier_e1_iff_rat.mpr classifiedD'E'
  exact And.intro realCarrierD'
    (And.intro realCarrierE'
      (And.intro realClassifierD'E' classifiedD'E'))

theorem RealAlgOrderConstant_algebra_row_obligations {d e o d' e' o' : BHist} :
    RatHistoryClassifier d d' -> RatHistoryClassifier e e' -> RatHistoryClassifier o o' ->
      RealConstantHistoryCarrier (BHist.e1 d) ∧
        RealConstantHistoryCarrier (BHist.e1 e) ∧
          RealConstantHistoryCarrier (BHist.e1 o) ∧
            RealConstantHistoryClassifier (BHist.e1 d) (BHist.e1 d') ∧
              RealConstantHistoryClassifier (BHist.e1 e) (BHist.e1 e') ∧
                RealConstantHistoryClassifier (BHist.e1 o) (BHist.e1 o') := by
  intro classifiedD classifiedE classifiedO
  have carrierD : RatHistoryCarrier d := classifiedD.left
  have carrierE : RatHistoryCarrier e := classifiedE.left
  have carrierO : RatHistoryCarrier o := classifiedO.left
  exact And.intro (RealConstantHistoryCarrier_e1_iff_rat.mpr carrierD)
    (And.intro (RealConstantHistoryCarrier_e1_iff_rat.mpr carrierE)
      (And.intro (RealConstantHistoryCarrier_e1_iff_rat.mpr carrierO)
        (And.intro (RealConstantHistoryClassifier_e1_iff_rat.mpr classifiedD)
          (And.intro (RealConstantHistoryClassifier_e1_iff_rat.mpr classifiedE)
            (RealConstantHistoryClassifier_e1_iff_rat.mpr classifiedO)))))

theorem RealAlgOrderConstant_rational_order_boundary {d e o d' e' o' : BHist} :
    RatHistoryClassifier d e -> RatHistoryClassifier e o -> hsame d d' -> hsame e e' ->
      hsame o o' ->
        RealConstantHistoryCarrier (BHist.e1 d') ∧
          RealConstantHistoryCarrier (BHist.e1 e') ∧
            RealConstantHistoryCarrier (BHist.e1 o') ∧
              RealConstantHistoryClassifier (BHist.e1 d') (BHist.e1 e') ∧
                RealConstantHistoryClassifier (BHist.e1 e') (BHist.e1 o') ∧
                  RatHistoryClassifier d' o' := by
  intro classifiedDE classifiedEO sameD sameE sameO
  have classifiedD'E' : RatHistoryClassifier d' e' :=
    RatHistoryClassifier_hsame_transport sameD sameE classifiedDE
  have classifiedE'O' : RatHistoryClassifier e' o' :=
    RatHistoryClassifier_hsame_transport sameE sameO classifiedEO
  have classifiedD'O' : RatHistoryClassifier d' o' :=
    RatHistoryClassifier_trans classifiedD'E' classifiedE'O'
  exact And.intro (RealConstantHistoryCarrier_e1_iff_rat.mpr classifiedD'E'.left)
    (And.intro (RealConstantHistoryCarrier_e1_iff_rat.mpr classifiedD'E'.right.left)
      (And.intro (RealConstantHistoryCarrier_e1_iff_rat.mpr classifiedE'O'.right.left)
        (And.intro (RealConstantHistoryClassifier_e1_iff_rat.mpr classifiedD'E')
          (And.intro (RealConstantHistoryClassifier_e1_iff_rat.mpr classifiedE'O')
            classifiedD'O'))))

theorem RealAlgOrderConstant_order_apartness_obligations {d e d' e' : BHist} :
    RatHistoryClassifier d d' -> RatHistoryClassifier e e' ->
      RealConstantHistoryCarrier (BHist.e1 d) ∧
        RealConstantHistoryCarrier (BHist.e1 d') ∧
          RealConstantHistoryCarrier (BHist.e1 e) ∧
            RealConstantHistoryCarrier (BHist.e1 e') ∧
              RealConstantHistoryClassifier (BHist.e1 d) (BHist.e1 d') ∧
                RealConstantHistoryClassifier (BHist.e1 e) (BHist.e1 e') := by
  intro classifiedD classifiedE
  exact And.intro (RealConstantHistoryCarrier_e1_iff_rat.mpr classifiedD.left)
    (And.intro (RealConstantHistoryCarrier_e1_iff_rat.mpr classifiedD.right.left)
      (And.intro (RealConstantHistoryCarrier_e1_iff_rat.mpr classifiedE.left)
        (And.intro (RealConstantHistoryCarrier_e1_iff_rat.mpr classifiedE.right.left)
          (And.intro (RealConstantHistoryClassifier_e1_iff_rat.mpr classifiedD)
            (RealConstantHistoryClassifier_e1_iff_rat.mpr classifiedE)))))

theorem RealAlgOrderConstant_rational_scoped_certificate {d e o d' e' o' : BHist} :
    RatHistoryClassifier d d' -> RatHistoryClassifier e e' -> RatHistoryClassifier o o' ->
      RatHistoryClassifier d e -> RatHistoryClassifier e o ->
        RealConstantHistoryCarrier (BHist.e1 d) ∧
          RealConstantHistoryCarrier (BHist.e1 d') ∧
            RealConstantHistoryCarrier (BHist.e1 e) ∧
              RealConstantHistoryCarrier (BHist.e1 e') ∧
                RealConstantHistoryCarrier (BHist.e1 o) ∧
                  RealConstantHistoryCarrier (BHist.e1 o') ∧
                    RealConstantHistoryClassifier (BHist.e1 d) (BHist.e1 d') ∧
                      RealConstantHistoryClassifier (BHist.e1 e) (BHist.e1 e') ∧
                        RealConstantHistoryClassifier (BHist.e1 o) (BHist.e1 o') ∧
                          RatHistoryClassifier d o := by
  intro classifiedD classifiedE classifiedO classifiedDE classifiedEO
  have classifiedDO : RatHistoryClassifier d o :=
    RatHistoryClassifier_trans classifiedDE classifiedEO
  exact And.intro (RealConstantHistoryCarrier_e1_iff_rat.mpr classifiedD.left)
    (And.intro (RealConstantHistoryCarrier_e1_iff_rat.mpr classifiedD.right.left)
      (And.intro (RealConstantHistoryCarrier_e1_iff_rat.mpr classifiedE.left)
        (And.intro (RealConstantHistoryCarrier_e1_iff_rat.mpr classifiedE.right.left)
          (And.intro (RealConstantHistoryCarrier_e1_iff_rat.mpr classifiedO.left)
            (And.intro (RealConstantHistoryCarrier_e1_iff_rat.mpr classifiedO.right.left)
              (And.intro (RealConstantHistoryClassifier_e1_iff_rat.mpr classifiedD)
                (And.intro (RealConstantHistoryClassifier_e1_iff_rat.mpr classifiedE)
                  (And.intro (RealConstantHistoryClassifier_e1_iff_rat.mpr classifiedO)
                    classifiedDO))))))))

end BEDC.Derived.RealAlgOrderUp
