namespace BEDC.Derived.SumUp

def SumCarrier (A B : Type) := Sum A B

def SumClassifierSpec {A B : Type} (sameA : A → A → Prop) (sameB : B → B → Prop) :
    SumCarrier A B → SumCarrier A B → Prop
  | Sum.inl a, Sum.inl a' => sameA a a'
  | Sum.inr b, Sum.inr b' => sameB b b'
  | Sum.inl _, Sum.inr _ => False
  | Sum.inr _, Sum.inl _ => False

theorem sum_stability_certificate_fields {A B : Type} {sameA : A → A → Prop}
    {sameB : B → B → Prop} (reflA : ∀ a, sameA a a) (reflB : ∀ b, sameB b b)
    (transA : ∀ {a b c}, sameA a b → sameA b c → sameA a c)
    (transB : ∀ {a b c}, sameB a b → sameB b c → sameB a c) :
    (∀ a : A, SumClassifierSpec sameA sameB (Sum.inl a) (Sum.inl a)) ∧
      (∀ b : B, SumClassifierSpec sameA sameB (Sum.inr b) (Sum.inr b)) ∧
      (∀ {x y z : SumCarrier A B},
        SumClassifierSpec sameA sameB x y →
          SumClassifierSpec sameA sameB y z →
            SumClassifierSpec sameA sameB x z) ∧
      (∀ (a : A) (b : B), SumClassifierSpec sameA sameB (Sum.inl a) (Sum.inr b) →
        False) ∧
      (∀ (a : A) (b : B), SumClassifierSpec sameA sameB (Sum.inr b) (Sum.inl a) →
        False) := by
  constructor
  · intro a
    exact reflA a
  · constructor
    · intro b
      exact reflB b
    · constructor
      · intro x y z hxy hyz
        cases x with
        | inl _ =>
            cases y with
            | inl _ =>
                cases z with
                | inl _ =>
                    exact transA hxy hyz
                | inr _ =>
                    exact hyz
            | inr _ =>
                cases hxy
        | inr _ =>
            cases y with
            | inl _ =>
                cases hxy
            | inr _ =>
                cases z with
                | inl _ =>
                    exact hyz
                | inr _ =>
                    exact transB hxy hyz
      · constructor
        · intro a b h
          exact h
        · intro a b h
          exact h

theorem SumClassifierSpec_trans {A B : Type} {RelA : A → A → Prop}
    {RelB : B → B → Prop}
    (relA_trans : ∀ {a b c : A}, RelA a b → RelA b c → RelA a c)
    (relB_trans : ∀ {a b c : B}, RelB a b → RelB b c → RelB a c) :
    ∀ {x y z : Sum A B},
      SumClassifierSpec RelA RelB x y →
        SumClassifierSpec RelA RelB y z →
          SumClassifierSpec RelA RelB x z := by
  intro x y z hxy hyz
  cases x <;> cases y <;> cases z <;> simp [SumClassifierSpec] at *
  · exact relA_trans hxy hyz
  · exact relB_trans hxy hyz

theorem sum_classifier_inversion {A B : Type} {sameA : A → A → Prop}
    {sameB : B → B → Prop} {x y : Sum A B} :
    SumClassifierSpec sameA sameB x y →
      (∃ a : A, ∃ a' : A, x = Sum.inl a ∧ y = Sum.inl a' ∧ sameA a a') ∨
        (∃ b : B, ∃ b' : B, x = Sum.inr b ∧ y = Sum.inr b' ∧ sameB b b') := by
  intro h
  cases x with
  | inl a =>
      cases y with
      | inl a' =>
          exact Or.inl ⟨a, a', rfl, rfl, h⟩
      | inr b =>
          cases h
  | inr b =>
      cases y with
      | inl a =>
          cases h
      | inr b' =>
          exact Or.inr ⟨b, b', rfl, rfl, h⟩

end BEDC.Derived.SumUp
