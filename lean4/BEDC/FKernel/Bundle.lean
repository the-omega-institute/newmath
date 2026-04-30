/-! Probe bundles are internally generated records, not exposed host lists. -/
namespace BEDC.FKernel.Bundle

inductive ProbeBundle (PName : Type) where
  | Bnil
  | Bcons (p : PName) (b : ProbeBundle PName)

def InBundle {PName : Type} (p : PName) : ProbeBundle PName → Prop
  | .Bnil => False
  | .Bcons q b => p = q ∨ InBundle p b

theorem inBundle_nil_elim {PName : Type} {p : PName} :
    InBundle p (ProbeBundle.Bnil : ProbeBundle PName) → False := by
  intro h
  exact h

theorem inBundle_nil_false {PName : Type} {p : PName} :
    InBundle p (ProbeBundle.Bnil : ProbeBundle PName) → False := by
  intro h
  exact h

theorem inBundle_cons_self {PName : Type} (p : PName) (tail : ProbeBundle PName) :
    InBundle p (ProbeBundle.Bcons p tail) := by
  exact Or.inl rfl

theorem inBundle_cons_tail {PName : Type} {p q : PName} {tail : ProbeBundle PName} :
    InBundle p tail -> InBundle p (ProbeBundle.Bcons q tail) := by
  intro h
  exact Or.inr h

theorem inBundle_cons_inversion {PName : Type} {p q : PName} {tail : ProbeBundle PName} :
    InBundle p (ProbeBundle.Bcons q tail) -> p = q \/ InBundle p tail := by
  intro h
  exact h

theorem inBundle_cons_cons_inversion {PName : Type} {x p q : PName}
    {tail : ProbeBundle PName} :
    InBundle x (ProbeBundle.Bcons p (ProbeBundle.Bcons q tail)) →
      x = p ∨ x = q ∨ InBundle x tail := by
  intro h
  exact h

end BEDC.FKernel.Bundle
