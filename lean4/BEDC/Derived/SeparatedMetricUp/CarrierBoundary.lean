import BEDC.Derived.SeparatedMetricUp.TasteGate

namespace BEDC.Derived.SeparatedMetricUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem SeparatedMetricCarrier_boundary
    (metric distance separation limit0 limit1 equivalence transport replay provenance
      name : BHist) :
    separatedMetricFields
        (SeparatedMetricUp.mk metric distance separation limit0 limit1 equivalence transport
          replay provenance name) =
        [metric, distance, separation, limit0, limit1, equivalence, transport, replay,
          provenance, name] ∧
      Cont metric distance (append metric distance) ∧
        Cont separation equivalence (append separation equivalence) ∧
          hsame (separatedMetricDecodeBHist (separatedMetricEncodeBHist metric)) metric ∧
            hsame (separatedMetricDecodeBHist (separatedMetricEncodeBHist distance)) distance := by
  -- BEDC touchpoint anchor: BHist Cont hsame append
  have metricRound :
      hsame (separatedMetricDecodeBHist (separatedMetricEncodeBHist metric)) metric := by
    induction metric with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  have distanceRound :
      hsame (separatedMetricDecodeBHist (separatedMetricEncodeBHist distance)) distance := by
    induction distance with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  exact
    ⟨rfl, cont_intro rfl, cont_intro rfl, metricRound, distanceRound⟩

end BEDC.Derived.SeparatedMetricUp
