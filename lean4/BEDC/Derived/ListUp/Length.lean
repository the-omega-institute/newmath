import BEDC.Derived.ListUp

namespace BEDC.Derived.ListUp

theorem ListClassifierSpec_length_eq {A : Type} {sameA : A → A → Prop} :
    ∀ {xs ys : BEDC.Derived.ListUp.ListCarrier A},
      BEDC.Derived.ListUp.ListClassifierSpec sameA xs ys → xs.length = ys.length := by
  intro xs
  induction xs with
  | nil =>
      intro ys classified
      cases ys with
      | nil =>
          rfl
      | cons _ _ =>
          cases classified
  | cons _ xs ih =>
      intro ys classified
      cases ys with
      | nil =>
          cases classified
      | cons _ ys =>
          cases classified with
          | intro _ tailClassified =>
              exact congrArg Nat.succ (ih tailClassified)

end BEDC.Derived.ListUp
