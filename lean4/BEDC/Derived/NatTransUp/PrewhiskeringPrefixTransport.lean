import BEDC.Derived.NatTransUp

namespace BEDC.Derived.NatTransUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp
open BEDC.Derived.FunctorUp

theorem NatTransPrefixComponentCarrier_prewhiskering_prefix_transport
    {pref p q a eta : BHist} :
    UnaryHistory pref -> NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier (append pref p) (append pref q) a eta ∧
        UnaryHistory (append pref p) ∧ UnaryHistory (append pref q) := by
  intro prefUnary component
  have sourceUnary : UnaryHistory (append pref p) :=
    unary_append_closed prefUnary component.left
  have targetUnary : UnaryHistory (append pref q) :=
    unary_append_closed prefUnary component.right.left
  have prefixedHom :
      CategoryHomCarrier (append pref (append p a)) (append pref (append q a)) eta :=
    FunctorPrefixHomCarrier_preserves prefUnary component.right.right.right
  have sourceSame : hsame (append pref (append p a)) (append (append pref p) a) :=
    (append_assoc pref p a).symm
  have targetSame : hsame (append pref (append q a)) (append (append pref q) a) :=
    (append_assoc pref q a).symm
  have transportedHom :
      CategoryHomCarrier (append (append pref p) a) (append (append pref q) a) eta :=
    CategoryHomCarrier_hsame_transport sourceSame targetSame (hsame_refl eta) prefixedHom
  exact
    ⟨⟨sourceUnary, targetUnary, component.right.right.left, transportedHom⟩,
      sourceUnary,
      targetUnary⟩

end BEDC.Derived.NatTransUp
