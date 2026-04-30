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

theorem cont_unit_laws :
    (∀ k : BHist, Cont .Empty k k) ∧
      (∀ {h r : BHist}, Cont h .Empty r → hsame r h) := by
  constructor
  · exact cont_left_unit
  · intro h r hr
    exact cont_deterministic hr (cont_right_unit h)

theorem cont_assoc_exists :
    ∀ {a b c ab bc : BHist},
      Cont a b ab → Cont b c bc → ∃ abc : BHist, Cont ab c abc ∧ Cont a bc abc := by
  intro a b c ab bc hab hbc
  refine ⟨append ab c, rfl, ?_⟩
  cases hab
  cases hbc
  simpa [Cont] using append_assoc a b c

theorem cont_assoc_middle_exists :
    ∀ {a b c ab abc : BHist}, Cont a b ab → Cont ab c abc → ∃ bc : BHist, Cont b c bc ∧ Cont a bc abc := by
  intro a b c ab abc hab habc
  cases hab
  cases habc
  exact ⟨append b c, rfl, append_assoc a b c⟩

theorem cont_assoc_relational {h k l u v w z : BHist} :
    Cont h k u -> Cont u l v -> Cont k l w -> Cont h w z -> hsame v z := by
  intro hku hulv klw hwz
  cases hku
  cases hulv
  cases klw
  cases hwz
  exact append_assoc h k l

end BEDC.FKernel.Cont
