/-! Probe bundles are internally generated records, not exposed host lists. -/
namespace BEDC.FKernel.Bundle

inductive ProbeBundle (PName : Type) where
  | Bnil
  | Bcons (p : PName) (b : ProbeBundle PName)

def InBundle {PName : Type} (p : PName) : ProbeBundle PName → Prop
  | .Bnil => False
  | .Bcons q b => p = q ∨ InBundle p b

end BEDC.FKernel.Bundle
