import BEDC.FKernel.Hist

/-! Relational continuation combines histories without exposing host concatenation. -/
namespace BEDC.FKernel.Cont

open BEDC.FKernel.Hist

def append : BHist → BHist → BHist
  | h, .Empty => h
  | h, .e0 k => .e0 (append h k)
  | h, .e1 k => .e1 (append h k)

theorem append_empty_right : ∀ h : BHist, append h .Empty = h := by
  intro h
  rfl

theorem append_empty_left : forall h : BHist, append .Empty h = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      simp [append, ih]
  | e1 h ih =>
      simp [append, ih]

def Cont (h k r : BHist) : Prop := r = append h k

theorem cont_iff_append {h k r : BHist} : Cont h k r <-> r = append h k := by
  rfl

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

theorem cont_right_constructor_inversion {h k r : BHist} :
    Cont h k r ->
      (k = BHist.Empty ∧ r = h) ∨
        (∃ k0 : BHist, ∃ r0 : BHist, k = BHist.e0 k0 ∧ r = BHist.e0 r0 ∧ Cont h k0 r0) ∨
          (∃ k0 : BHist, ∃ r0 : BHist, k = BHist.e1 k0 ∧ r = BHist.e1 r0 ∧ Cont h k0 r0) := by
  intro hr
  cases k with
  | Empty =>
      left
      constructor
      · rfl
      · exact hr
  | e0 k0 =>
      right
      left
      exact ⟨k0, append h k0, rfl, by simpa [Cont, append] using hr, rfl⟩
  | e1 k0 =>
      right
      right
      exact ⟨k0, append h k0, rfl, by simpa [Cont, append] using hr, rfl⟩

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

theorem cont_assoc_left_exists {h k l u v : BHist} :
    Cont h k u -> Cont u l v -> exists w : BHist, Cont k l w /\ Cont h w v := by
  intro hku huv
  cases hku
  cases huv
  exact Exists.intro (append k l) (And.intro rfl (append_assoc h k l))

theorem cont_assoc_relational {h k l u v w z : BHist} :
    Cont h k u -> Cont u l v -> Cont k l w -> Cont h w z -> hsame v z := by
  intro hku hulv klw hwz
  cases hku
  cases hulv
  cases klw
  cases hwz
  exact append_assoc h k l

theorem cont_assoc_unique {a b c ab bc abc abc' : BHist} :
    Cont a b ab -> Cont b c bc -> Cont ab c abc -> Cont a bc abc' -> hsame abc abc' := by
  intro hab hbc habc habc'
  cases hab
  cases hbc
  cases habc
  cases habc'
  exact append_assoc a b c

end BEDC.FKernel.Cont
