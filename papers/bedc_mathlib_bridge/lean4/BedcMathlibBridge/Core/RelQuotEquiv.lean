namespace BedcMathlibBridge

universe u v

/--
A BEDC carrier `A` with relation `RA` corresponds to mathlib carrier `B`, where the inverse
from mathlib returns only up to `RA`.
-/
structure RelQuotEquiv (A : Type u) (RA : A → A → Prop) (B : Type v) where
  toM : A → B
  ofM : B → A
  leftInvRel : ∀ a, RA (ofM (toM a)) a
  rightInv : ∀ b, toM (ofM b) = b
  relIff : ∀ a a', RA a a' ↔ toM a = toM a'

end BedcMathlibBridge
