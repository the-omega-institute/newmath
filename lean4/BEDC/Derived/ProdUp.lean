namespace BEDC.Derived.ProdUp

def ProdCarrier (A B : Type) := Prod A B

def ProdClassifierSpec {A B : Type} (sameA : A → A → Prop) (sameB : B → B → Prop)
    (x y : ProdCarrier A B) : Prop :=
  sameA x.1 y.1 ∧ sameB x.2 y.2

theorem prod_stability_certificate_fields {A B : Type} {sameA : A → A → Prop}
    {sameB : B → B → Prop} (reflA : ∀ a, sameA a a) (reflB : ∀ b, sameB b b)
    (transA : ∀ {a b c}, sameA a b → sameA b c → sameA a c)
    (transB : ∀ {a b c}, sameB a b → sameB b c → sameB a c) :
    (∀ x : ProdCarrier A B, ProdClassifierSpec sameA sameB x x) ∧
      (∀ {x y z : ProdCarrier A B},
        ProdClassifierSpec sameA sameB x y →
          ProdClassifierSpec sameA sameB y z →
            ProdClassifierSpec sameA sameB x z) ∧
      (∀ {x y : ProdCarrier A B},
        ProdClassifierSpec sameA sameB x y → sameA x.1 y.1 ∧ sameB x.2 y.2) := by
  constructor
  · intro x
    cases x with
    | mk a b =>
        constructor
        · exact reflA a
        · exact reflB b
  · constructor
    · intro x y z hxy hyz
      cases x with
      | mk xa xb =>
          cases y with
          | mk ya yb =>
              cases z with
              | mk za zb =>
                  cases hxy with
                  | intro hAxy hBxy =>
                      cases hyz with
                      | intro hAyz hByz =>
                          constructor
                          · exact transA hAxy hAyz
                          · exact transB hBxy hByz
    · intro x y hxy
      exact hxy

end BEDC.Derived.ProdUp
