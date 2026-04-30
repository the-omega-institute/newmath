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

theorem inBundle_cons_of_eq {PName : Type} {p q : PName} {tail : ProbeBundle PName} :
    p = q -> InBundle p (ProbeBundle.Bcons q tail) := by
  intro hp
  exact Or.inl hp

theorem inBundle_cons_tail {PName : Type} {p q : PName} {tail : ProbeBundle PName} :
    InBundle p tail -> InBundle p (ProbeBundle.Bcons q tail) := by
  intro h
  exact Or.inr h

theorem inBundle_cons_cons_tail {PName : Type} {x p q : PName}
    {tail : ProbeBundle PName} :
    InBundle x tail → InBundle x (ProbeBundle.Bcons p (ProbeBundle.Bcons q tail)) := by
  intro h
  exact Or.inr (Or.inr h)

theorem inBundle_cons_inversion {PName : Type} {p q : PName} {tail : ProbeBundle PName} :
    InBundle p (ProbeBundle.Bcons q tail) -> p = q \/ InBundle p tail := by
  intro h
  exact h

theorem inBundle_cons_iff {PName : Type} {p q : PName} {tail : ProbeBundle PName} :
    InBundle p (ProbeBundle.Bcons q tail) ↔ p = q ∨ InBundle p tail := by
  rfl

theorem inBundle_cons_cons_inversion {PName : Type} {x p q : PName}
    {tail : ProbeBundle PName} :
    InBundle x (ProbeBundle.Bcons p (ProbeBundle.Bcons q tail)) →
      x = p ∨ x = q ∨ InBundle x tail := by
  intro h
  exact h

theorem inBundle_nonempty_from_membership {PName : Type} {p : PName} :
    ∀ {bundle : ProbeBundle PName}, InBundle p bundle →
      ∃ q : PName, ∃ tail : ProbeBundle PName, bundle = ProbeBundle.Bcons q tail := by
  intro bundle h
  cases bundle with
  | Bnil =>
      exact False.elim h
  | Bcons q tail =>
      exact ⟨q, tail, rfl⟩

theorem bundle_generation_cases {PName : Type} (bundle : ProbeBundle PName) :
    bundle = ProbeBundle.Bnil ∨
      ∃ p : PName, ∃ tail : ProbeBundle PName, bundle = ProbeBundle.Bcons p tail := by
  cases bundle with
  | Bnil =>
      exact Or.inl rfl
  | Bcons p tail =>
      exact Or.inr ⟨p, tail, rfl⟩

theorem probeBundle_generated_induction {PName : Type} {M : ProbeBundle PName → Prop} :
    M ProbeBundle.Bnil →
      (∀ p tail, M tail → M (ProbeBundle.Bcons p tail)) →
        ∀ bundle, M bundle := by
  intro hnil hcons bundle
  induction bundle with
  | Bnil =>
      exact hnil
  | Bcons p tail ih =>
      exact hcons p tail ih

end BEDC.FKernel.Bundle
