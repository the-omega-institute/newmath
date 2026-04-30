import BEDC.FKernel.Bundle

namespace BEDC.FKernel.Bundle

theorem inBundle_bundleAppend_left_of_not_right {PName : Type} {p : PName}
    {left right : ProbeBundle PName} :
    InBundle p (bundleAppend left right) -> (InBundle p right -> False) -> InBundle p left := by
  induction left with
  | Bnil =>
      intro inAppend notRight
      exact False.elim (notRight inAppend)
  | Bcons q tail ih =>
      intro inAppend notRight
      cases inAppend with
      | inl head =>
          exact Or.inl head
      | inr tailOrRight =>
          exact Or.inr (ih tailOrRight notRight)

end BEDC.FKernel.Bundle
