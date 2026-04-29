import BEDC.FKernel.Hist

/-! Relational continuation combines histories without exposing host concatenation. -/
namespace BEDC.FKernel.Cont

open BEDC.FKernel.Hist

def append : BHist → BHist → BHist
  | h, .Empty => h
  | h, .e0 k => .e0 (append h k)
  | h, .e1 k => .e1 (append h k)

def Cont (h k r : BHist) : Prop := r = append h k

theorem append_assoc : ∀ a b c : BHist, append (append a b) c = append a (append b c) := by
  intro a b c
  induction c with
  | Empty =>
      rfl
  | e0 c ih =>
      simp [append, ih]
  | e1 c ih =>
      simp [append, ih]

theorem cont_deterministic :
    ∀ {h k r r' : BHist}, Cont h k r → Cont h k r' → hsame r r' := by
  intro h k r r' hr hr'
  exact hr.trans hr'.symm

theorem cont_left_unit : ∀ k : BHist, Cont .Empty k k := by
  intro k
  induction k with
  | Empty =>
      rfl
  | e0 k ih =>
      simpa [Cont, append] using congrArg BHist.e0 ih
  | e1 k ih =>
      simpa [Cont, append] using congrArg BHist.e1 ih

theorem cont_right_unit : ∀ h : BHist, Cont h .Empty h := by
  intro h
  rfl

theorem cont_assoc_exists :
    ∀ {a b c ab bc : BHist},
      Cont a b ab → Cont b c bc → ∃ abc : BHist, Cont ab c abc ∧ Cont a bc abc := by
  intro a b c ab bc hab hbc
  refine ⟨append ab c, rfl, ?_⟩
  cases hab
  cases hbc
  simpa [Cont] using append_assoc a b c

end BEDC.FKernel.Cont
