import BEDC.Derived.S1Up

namespace BEDC.Derived.S1Up

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp
open BEDC.Derived.RealUp

theorem SOneHistoryCarrier_e1_components_carrier_exactness {dx dy equationTail t : BHist} :
    SOneHistoryCarrier (BHist.e1 dx) (BHist.e1 dy) (BHist.e1 equationTail) (BHist.e1 t) ↔
      RatHistoryCarrier dx ∧ RatHistoryCarrier dy ∧
        RatHistoryClassifier equationTail (BHist.e1 BHist.Empty) ∧
          Cont (BHist.e1 dx) dy t := by
  constructor
  · intro carrier
    exact SOneHistoryCarrier_e1_components_unit_equation_classifier carrier
  · intro fields
    have xCarrier : RealConstantHistoryCarrier (BHist.e1 dx) :=
      RealConstantHistoryCarrier_e1_iff_rat.mpr fields.left
    have yCarrier : RealConstantHistoryCarrier (BHist.e1 dy) :=
      RealConstantHistoryCarrier_e1_iff_rat.mpr fields.right.left
    have equationCarrier :
        RealConstantHistoryClassifier (BHist.e1 equationTail) SOneUnitHistory := by
      change RealConstantHistoryClassifier (BHist.e1 equationTail)
        (BHist.e1 (BHist.e1 BHist.Empty))
      exact RealConstantHistoryClassifier_e1_iff_rat.mpr fields.right.right.left
    have pointCont : Cont (BHist.e1 dx) (BHist.e1 dy) (BHist.e1 t) :=
      cont_step_one fields.right.right.right
    exact And.intro xCarrier (And.intro yCarrier (And.intro equationCarrier pointCont))

end BEDC.Derived.S1Up
