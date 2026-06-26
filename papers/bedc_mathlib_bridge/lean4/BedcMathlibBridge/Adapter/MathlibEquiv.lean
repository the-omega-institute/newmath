import Mathlib.Logic.Equiv.Defs
import BedcMathlibBridge.Core.RelEquiv

namespace BedcMathlibBridge

universe u v

/-- A relation-level bridge induces the underlying mathlib type equivalence. -/
def RelEquiv.toEquiv {A : Type u} {RA : A → A → Prop} {B : Type v}
    (e : RelEquiv A RA B) : A ≃ B :=
  ⟨e.toM, e.ofM, e.leftInv, e.rightInv⟩

end BedcMathlibBridge
