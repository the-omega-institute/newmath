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
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def Cont (h k r : BHist) : Prop := r = append h k

theorem cont_intro {h k r : BHist} (hr : r = append h k) : Cont h k r := by
  exact hr

theorem cont_iff_append {h k r : BHist} : Cont h k r <-> r = append h k := by
  rfl

theorem cont_right_step_rules {h k r : BHist} :
    Cont h k r → Cont h (BHist.e0 k) (BHist.e0 r) ∧ Cont h (BHist.e1 k) (BHist.e1 r) := by
  intro hr
  constructor
  · cases hr
    rfl
  · cases hr
    rfl

theorem cont_step_zero {h k r : BHist} :
    Cont h k r -> Cont h (BHist.e0 k) (BHist.e0 r) := by
  intro hr
  exact (cont_right_step_rules hr).left

theorem cont_step_one {h k r : BHist} :
    Cont h k r -> Cont h (BHist.e1 k) (BHist.e1 r) := by
  intro hr
  exact (cont_right_step_rules hr).right

theorem cont_step_rules_pair :
    (forall {h k r : BHist}, Cont h k r -> Cont h (.e0 k) (.e0 r)) /\
      (forall {h k r : BHist}, Cont h k r -> Cont h (.e1 k) (.e1 r)) := by
  constructor
  · intro h k r hcont
    exact cont_step_zero hcont
  · intro h k r hcont
    exact cont_step_one hcont

theorem append_assoc : ∀ a b c : BHist, append (append a b) c = append a (append b c) := by
  intro a b c
  induction c with
  | Empty =>
      rfl
  | e0 c ih =>
      exact congrArg BHist.e0 ih
  | e1 c ih =>
      exact congrArg BHist.e1 ih

theorem append_right_cancel :
    ∀ {h h' k : BHist}, append h k = append h' k → hsame h h' := by
  intro h h' k same
  induction k generalizing h h' with
  | Empty =>
      exact same
  | e0 k ih =>
      exact ih (BHist.e0.inj same)
  | e1 k ih =>
      exact ih (BHist.e1.inj same)

private def appendCancelLength : BHist → Nat
  | .Empty => 0
  | .e0 h => Nat.succ (appendCancelLength h)
  | .e1 h => Nat.succ (appendCancelLength h)

private theorem append_length :
    ∀ h k : BHist, appendCancelLength (append h k) =
      appendCancelLength h + appendCancelLength k := by
  intro h k
  induction k with
  | Empty =>
      rfl
  | e0 k ih =>
      exact congrArg Nat.succ ih
  | e1 k ih =>
      exact congrArg Nat.succ ih

private theorem nat_eq_add_succ_false (n m : Nat) : n = n + m + 1 → False := by
  intro h
  exact (Nat.lt_irrefl n) (Nat.lt_of_lt_of_eq (Nat.lt_add_of_pos_right (Nat.succ_pos m)) h.symm)

theorem append_left_cancel : ∀ {h k k' : BHist}, append h k = append h k' → hsame k k' := by
  intro h k
  induction k generalizing h with
  | Empty =>
      intro k' same
      cases k' with
      | Empty =>
          rfl
      | e0 k' =>
          have hlen := congrArg appendCancelLength same
          simp [append, appendCancelLength, append_length] at hlen
          exact False.elim (nat_eq_add_succ_false (appendCancelLength h) (appendCancelLength k') hlen)
      | e1 k' =>
          have hlen := congrArg appendCancelLength same
          simp [append, appendCancelLength, append_length] at hlen
          exact False.elim (nat_eq_add_succ_false (appendCancelLength h) (appendCancelLength k') hlen)
  | e0 k ih =>
      intro k' same
      cases k' with
      | Empty =>
          have hlen := congrArg appendCancelLength same
          simp [append, appendCancelLength, append_length] at hlen
          exact False.elim (nat_eq_add_succ_false (appendCancelLength h) (appendCancelLength k) hlen.symm)
      | e0 k' =>
          exact congrArg BHist.e0 (ih (h := h) (k' := k') (BHist.e0.inj same))
      | e1 k' =>
          cases same
  | e1 k ih =>
      intro k' same
      cases k' with
      | Empty =>
          have hlen := congrArg appendCancelLength same
          simp [append, appendCancelLength, append_length] at hlen
          exact False.elim (nat_eq_add_succ_false (appendCancelLength h) (appendCancelLength k) hlen.symm)
      | e0 k' =>
          cases same
      | e1 k' =>
          exact congrArg BHist.e1 (ih (h := h) (k' := k') (BHist.e1.inj same))

theorem cont_right_cancel :
    ∀ {h h' k r : BHist}, Cont h k r → Cont h' k r → hsame h h' := by
  intro h h' k r left right
  apply append_right_cancel (k := k)
  exact left.symm.trans right

theorem cont_left_cancel :
    forall {h k k' r : BHist}, Cont h k r -> Cont h k' r -> hsame k k' := by
  intro h k k' r left right
  apply append_left_cancel (h := h)
  exact left.symm.trans right

theorem cont_deterministic :
    ∀ {h k r r' : BHist}, Cont h k r → Cont h k r' → hsame r r' := by
  intro h k r r' hr hr'
  exact hr.trans hr'.symm

theorem cont_respects_hsame {h h' k k' r r' : BHist} :
    hsame h h' -> hsame k k' -> Cont h k r -> Cont h' k' r' -> hsame r r' := by
  intro hh hk hr hr'
  cases hh
  cases hk
  exact cont_deterministic hr hr'

theorem cont_left_unit : ∀ k : BHist, Cont .Empty k k := by
  intro k
  induction k with
  | Empty =>
      rfl
  | e0 k ih =>
      change BHist.e0 k = BHist.e0 (append BHist.Empty k)
      exact congrArg BHist.e0 ih
  | e1 k ih =>
      change BHist.e1 k = BHist.e1 (append BHist.Empty k)
      exact congrArg BHist.e1 ih

theorem cont_left_unit_result {k r : BHist} : Cont BHist.Empty k r -> hsame r k := by
  intro hr
  exact cont_deterministic hr (cont_left_unit k)

theorem cont_left_unit_unique : forall {h k : BHist}, Cont h k k -> hsame h BHist.Empty := by
  intro h k hk
  induction k generalizing h with
  | Empty =>
      exact hk.symm
  | e0 k ih =>
      exact ih (BHist.e0.inj hk)
  | e1 k ih =>
      exact ih (BHist.e1.inj hk)

theorem cont_right_unit : ∀ h : BHist, Cont h .Empty h := by
  intro h
  rfl

theorem cont_relation_generated_rules :
    (forall h : BHist, Cont h .Empty h) /\
      (forall {h k r : BHist}, Cont h k r -> Cont h (.e0 k) (.e0 r)) /\
      (forall {h k r : BHist}, Cont h k r -> Cont h (.e1 k) (.e1 r)) := by
  constructor
  · exact cont_right_unit
  · constructor
    · intro h k r hcont
      exact cont_step_zero hcont
    · intro h k r hcont
      exact cont_step_one hcont

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
      exact ⟨k0, append h k0, rfl, hr, rfl⟩
  | e1 k0 =>
      right
      right
      exact ⟨k0, append h k0, rfl, hr, rfl⟩

theorem cont_empty_result_inversion {h k : BHist} :
    Cont h k BHist.Empty -> h = BHist.Empty ∧ k = BHist.Empty := by
  intro hc
  cases k with
  | Empty =>
      constructor
      · exact hc.symm
      · rfl
  | e0 k0 =>
      cases hc
  | e1 k0 =>
      cases hc

theorem cont_e1_result_inversion {h k r : BHist} :
    Cont h k (BHist.e1 r) ->
      (k = BHist.Empty ∧ hsame h (BHist.e1 r)) ∨
        (∃ k0 : BHist, k = BHist.e1 k0 ∧ Cont h k0 r) := by
  intro hc
  cases k with
  | Empty =>
      left
      constructor
      · rfl
      · exact hc.symm
  | e0 k0 =>
      cases hc
  | e1 k0 =>
      right
      exact ⟨k0, rfl, BHist.e1.inj hc⟩

theorem cont_e0_result_inversion {h k r : BHist} :
    Cont h k (BHist.e0 r) ->
      (k = BHist.Empty ∧ hsame h (BHist.e0 r)) ∨
        (∃ k0 : BHist, k = BHist.e0 k0 ∧ Cont h k0 r) := by
  intro hc
  cases k with
  | Empty =>
      left
      constructor
      · rfl
      · exact hc.symm
  | e0 k0 =>
      right
      exact ⟨k0, rfl, BHist.e0.inj hc⟩
  | e1 k0 =>
      cases hc

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
  exact append_assoc a b c

theorem cont_assoc_exists_hsame {a b c ab bc : BHist} :
    Cont a b ab -> Cont b c bc ->
      exists left : BHist, exists right : BHist,
        Cont ab c left ∧ Cont a bc right ∧ hsame left right := by
  intro hab hbc
  cases hab
  cases hbc
  exact ⟨append (append a b) c, append a (append b c), rfl, rfl,
    append_assoc a b c⟩

theorem cont_assoc_middle_exists :
    ∀ {a b c ab abc : BHist}, Cont a b ab → Cont ab c abc → ∃ bc : BHist, Cont b c bc ∧ Cont a bc abc := by
  intro a b c ab abc hab habc
  cases hab
  cases habc
  exact ⟨append b c, rfl, append_assoc a b c⟩

theorem cont_assoc_forward_witness {a b c ab abc : BHist} :
    Cont a b ab -> Cont ab c abc ->
      exists bc : BHist, exists abc' : BHist,
        Cont b c bc /\ Cont a bc abc' /\ hsame abc abc' := by
  intro hab habc
  cases hab
  cases habc
  exact ⟨append b c, append a (append b c), rfl, rfl, append_assoc a b c⟩

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

theorem cont_assoc_primary {h k l u v w z : BHist} :
    Cont h k u -> Cont u l v -> Cont k l w -> Cont h w z -> hsame v z := by
  intro hku hulv klw hwz
  cases hku
  cases hulv
  cases klw
  cases hwz
  exact append_assoc h k l

theorem continuation_associativity {h k l u v w z : BHist} :
    Cont h k u -> Cont u l v -> Cont k l w -> Cont h w z -> hsame v z := by
  intro hku hulv klw hwz
  cases hku
  cases hulv
  cases klw
  cases hwz
  exact append_assoc h k l

theorem cont_assoc_hsame {a b c ab bc left right : BHist} :
    Cont a b ab -> Cont ab c left -> Cont b c bc -> Cont a bc right -> hsame left right := by
  intro hab hleft hbc hright
  cases hab
  cases hleft
  cases hbc
  cases hright
  exact append_assoc a b c

theorem cont_assoc_unique {a b c ab bc abc abc' : BHist} :
    Cont a b ab -> Cont b c bc -> Cont ab c abc -> Cont a bc abc' -> hsame abc abc' := by
  intro hab hbc habc habc'
  cases hab
  cases hbc
  cases habc
  cases habc'
  exact append_assoc a b c

theorem cont_addition_like_seed :
    (∀ h : BHist, Cont BHist.Empty h h) ∧
      (∀ h : BHist, Cont h BHist.Empty h) ∧
        (∀ {a b c ab bc abc abc' : BHist},
          Cont a b ab → Cont b c bc → Cont ab c abc → Cont a bc abc' → hsame abc abc') := by
  constructor
  · exact cont_left_unit
  · constructor
    · exact cont_right_unit
    · intro a b c ab bc abc abc' hab hbc habc habc'
      exact cont_assoc_unique hab hbc habc habc'

end BEDC.FKernel.Cont
