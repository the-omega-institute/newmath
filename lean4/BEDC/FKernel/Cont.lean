import BEDC.FKernel.Hist

/-! Relational continuation combines histories without exposing host concatenation. -/
namespace BEDC.FKernel.Cont

open BEDC.FKernel.Hist

axiom Cont : BHist → BHist → BHist → Prop

theorem cont_deterministic :
    ∀ {h k r r' : BHist}, Cont h k r → Cont h k r' → hsame r r' := by
  sorry

theorem cont_left_unit : ∀ k : BHist, Cont Empty k k := by
  sorry

theorem cont_right_unit : ∀ h : BHist, Cont h Empty h := by
  sorry

theorem cont_assoc_exists :
    ∀ {a b c ab bc : BHist},
      Cont a b ab → Cont b c bc → ∃ abc : BHist, Cont ab c abc ∧ Cont a bc abc := by
  sorry

end BEDC.FKernel.Cont
