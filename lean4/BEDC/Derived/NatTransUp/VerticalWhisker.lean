import BEDC.Derived.NatTransUp

namespace BEDC.Derived.NatTransUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp
open BEDC.Derived.FunctorUp

theorem NatTransPrefixComponentCarrier_prefix_vert_comp_closed {u p q r a eta theta composite : BHist} :
    UnaryHistory u -> NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q r a theta -> Cont eta theta composite ->
        NatTransPrefixComponentCarrier (append u p) (append u r) a composite := by
  intro prefixCarrier left right composition
  have baseComposite : CategoryHomCarrier (append p a) (append r a) composite :=
    CategoryHomCarrier_comp_closed left.right.right.right right.right.right.right composition
  have prefixedComposite :
      CategoryHomCarrier (append u (append p a)) (append u (append r a)) composite :=
    FunctorPrefixHomCarrier_preserves prefixCarrier baseComposite
  have sourceSame : hsame (append u (append p a)) (append (append u p) a) :=
    (append_assoc u p a).symm
  have targetSame : hsame (append u (append r a)) (append (append u r) a) :=
    (append_assoc u r a).symm
  exact And.intro (unary_append_closed prefixCarrier left.left)
    (And.intro (unary_append_closed prefixCarrier right.right.left)
      (And.intro left.right.right.left
        (CategoryHomCarrier_hsame_transport sourceSame targetSame (hsame_refl composite)
          prefixedComposite)))

theorem NatTransPrefixComponentCarrier_prefix_whiskering_vert_comp_public_readback
    {u p q r a eta theta composite displayed : BHist} :
    UnaryHistory u -> NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q r a theta -> Cont eta theta composite ->
        NatTransPrefixComponentCarrier (append u p) (append u r) a displayed ->
          hsame composite displayed := by
  intro prefixCarrier left right composition displayedCarrier
  have compositeCarrier :
      NatTransPrefixComponentCarrier (append u p) (append u r) a composite :=
    NatTransPrefixComponentCarrier_prefix_vert_comp_closed
      prefixCarrier left right composition
  exact CategoryHomCarrier_morphism_deterministic
    compositeCarrier.right.right.right displayedCarrier.right.right.right

end BEDC.Derived.NatTransUp
