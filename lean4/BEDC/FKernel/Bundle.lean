/-! Probe bundles are internally generated records, not exposed host lists. -/
namespace BEDC.FKernel.Bundle

inductive ProbeBundle (PName : Type) where
  | Bnil
  | Bcons (p : PName) (b : ProbeBundle PName)

def InBundle {PName : Type} (p : PName) : ProbeBundle PName → Prop
  | .Bnil => False
  | .Bcons q b => p = q ∨ InBundle p b

theorem inBundle_cons_self {PName : Type} (p : PName) (tail : ProbeBundle PName) :
    InBundle p (ProbeBundle.Bcons p tail) := by
  exact Or.inl rfl

end BEDC.FKernel.Bundle
