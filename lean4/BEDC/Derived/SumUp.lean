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

end BEDC.Derived.SumUp
