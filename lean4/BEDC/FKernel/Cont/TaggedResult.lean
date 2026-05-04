import BEDC.FKernel.Cont.Step

namespace BEDC.FKernel.Cont

open BEDC.FKernel.Hist

theorem cont_result_hsame_e0_cases {h k r z : BHist} :
    Cont h k r -> hsame r (BHist.e0 z) ->
      (k = BHist.Empty ∧ hsame h (BHist.e0 z)) ∨
        Exists (fun k0 : BHist => k = BHist.e0 k0 ∧ Cont h k0 z) := by
  intro hcont sameResult
  have taggedResult : Cont h k (BHist.e0 z) :=
    cont_result_hsame_transport hcont sameResult
  exact Iff.mp cont_result_e0_cases_iff taggedResult

theorem cont_result_hsame_e1_cases {h k r z : BHist} :
    Cont h k r -> hsame r (BHist.e1 z) ->
      (k = BHist.Empty ∧ hsame h (BHist.e1 z)) ∨
        Exists (fun k0 : BHist => k = BHist.e1 k0 ∧ Cont h k0 z) := by
  intro hcont sameResult
  have taggedResult : Cont h k (BHist.e1 z) :=
    cont_result_hsame_transport hcont sameResult
  exact Iff.mp cont_result_e1_cases_iff taggedResult

end BEDC.FKernel.Cont
