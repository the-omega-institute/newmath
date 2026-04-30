import BEDC.FKernel.Hist

namespace BEDC.Derived.ProdUp

def ProdCarrier (A B : Type) := Prod A B

def ProdClassifierSpec {A B : Type} (sameA : A → A → Prop) (sameB : B → B → Prop)
    (x y : ProdCarrier A B) : Prop :=
  sameA x.1 y.1 ∧ sameB x.2 y.2

def ProdClassifier {α β : Type} (left : α → α → Prop) (right : β → β → Prop)
    (x y : α × β) : Prop :=
  left x.1 y.1 ∧ right x.2 y.2

theorem prodClassifier_iff {α β : Type} {leftSame : α → α → Prop}
    {rightSame : β → β → Prop} {x y : ProdCarrier α β} :
    ProdClassifier leftSame rightSame x y ↔ leftSame x.1 y.1 ∧ rightSame x.2 y.2 := by
  constructor <;> intro h <;> exact h

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

theorem prodClassifierSpec_trans {A B : Type} {sameA : A -> A -> Prop}
    {sameB : B -> B -> Prop}
    (transA : forall {a b c : A}, sameA a b -> sameA b c -> sameA a c)
    (transB : forall {a b c : B}, sameB a b -> sameB b c -> sameB a c)
    {x y z : Prod A B} :
    ProdClassifierSpec sameA sameB x y ->
      ProdClassifierSpec sameA sameB y z -> ProdClassifierSpec sameA sameB x z := by
  intro hxy hyz
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
                      exact ⟨transA hAxy hAyz, transB hBxy hByz⟩

theorem prod_stability_certificate {A B : Type} {sameA : A -> A -> Prop}
    {sameB : B -> B -> Prop} (reflA : forall a : A, sameA a a)
    (reflB : forall b : B, sameB b b)
    (transA : forall {a b c : A}, sameA a b -> sameA b c -> sameA a c)
    (transB : forall {a b c : B}, sameB a b -> sameB b c -> sameB a c) :
    (forall x : A × B, sameA x.1 x.1 /\ sameB x.2 x.2) /\
      (forall {x y z : A × B}, (sameA x.1 y.1 /\ sameB x.2 y.2) ->
        (sameA y.1 z.1 /\ sameB y.2 z.2) ->
          (sameA x.1 z.1 /\ sameB x.2 z.2)) /\
        (forall {x y : A × B}, (sameA x.1 y.1 /\ sameB x.2 y.2) ->
          sameA x.1 y.1) /\
          (forall {x y : A × B}, (sameA x.1 y.1 /\ sameB x.2 y.2) ->
            sameB x.2 y.2) := by
  constructor
  · intro x
    constructor
    · exact reflA x.1
    · exact reflB x.2
  · constructor
    · intro x y z hxy hyz
      constructor
      · exact transA hxy.left hyz.left
      · exact transB hxy.right hyz.right
    · constructor
      · intro x y hxy
        exact hxy.left
      · intro x y hxy
        exact hxy.right

theorem ProdClassifierSpec_trans {A B : Type} {relA : A → A → Prop} {relB : B → B → Prop}
    (transA : ∀ {a b c : A}, relA a b → relA b c → relA a c)
    (transB : ∀ {a b c : B}, relB a b → relB b c → relB a c)
    {x y z : ProdCarrier A B} :
    ProdClassifierSpec relA relB x y →
      ProdClassifierSpec relA relB y z →
        ProdClassifierSpec relA relB x z := by
  intro hxy hyz
  cases hxy with
  | intro leftXY rightXY =>
      cases hyz with
      | intro leftYZ rightYZ =>
          constructor
          · exact transA leftXY leftYZ
          · exact transB rightXY rightYZ

theorem ProdClassifierSpec_hsame_symm
    {x y : ProdCarrier BEDC.FKernel.Hist.BHist BEDC.FKernel.Hist.BHist} :
    ProdClassifierSpec BEDC.FKernel.Hist.hsame BEDC.FKernel.Hist.hsame x y →
      ProdClassifierSpec BEDC.FKernel.Hist.hsame BEDC.FKernel.Hist.hsame y x := by
  intro hxy
  cases hxy with
  | intro leftXY rightXY =>
      constructor
      · exact BEDC.FKernel.Hist.hsame_symm leftXY
      · exact BEDC.FKernel.Hist.hsame_symm rightXY

end BEDC.Derived.ProdUp
