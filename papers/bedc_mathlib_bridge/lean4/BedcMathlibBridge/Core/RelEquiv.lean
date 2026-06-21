namespace BedcMathlibBridge

universe u v

/-- BEDC carrier `A` with relation `RA`, constructively corresponding to mathlib carrier `B`. -/
structure RelEquiv (A : Type u) (RA : A → A → Prop) (B : Type v) where
  toM : A → B
  ofM : B → A
  leftInv : ∀ a, ofM (toM a) = a
  rightInv : ∀ b, toM (ofM b) = b
  relIff : ∀ a a', RA a a' ↔ toM a = toM a'

end BedcMathlibBridge
