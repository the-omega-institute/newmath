import BEDC.Derived.NatTransUp

namespace BEDC.Derived.NatTransUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp
open BEDC.Derived.FunctorUp

theorem NatTransPrefixComponentCarrier_vert_comp_tail_comm_closed
    {p q r a eta theta etatheta thetaeta : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q r a theta ->
        Cont eta theta etatheta -> Cont theta eta thetaeta ->
          NatTransPrefixComponentCarrier p r a etatheta ∧ hsame etatheta thetaeta := by
  intro left right etathetaRel thetaetaRel
  exact
    And.intro
      (NatTransPrefixComponentCarrier_vert_comp_closed left right etathetaRel)
      (NatTransPrefixComponentCarrier_tail_comm_hsame left right etathetaRel thetaetaRel)

theorem NatTransPrefixComponentCarrier_vert_comp_tail_comm_public_readback
    {p q r a eta theta etatheta thetaeta displayed : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q r a theta ->
        Cont eta theta etatheta ->
          Cont theta eta thetaeta ->
            NatTransPrefixComponentCarrier p r a etatheta ∧
              NatTransPrefixComponentCarrier p r a thetaeta ∧
                hsame etatheta thetaeta ∧
                  (NatTransPrefixComponentCarrier p r a displayed ->
                    hsame etatheta displayed ∧ hsame thetaeta displayed) := by
  intro left right etathetaRel thetaetaRel
  have forwardCarrier : NatTransPrefixComponentCarrier p r a etatheta :=
    NatTransPrefixComponentCarrier_vert_comp_closed left right etathetaRel
  have sameTail : hsame etatheta thetaeta :=
    NatTransPrefixComponentCarrier_tail_comm_hsame left right etathetaRel thetaetaRel
  have reverseCarrier : NatTransPrefixComponentCarrier p r a thetaeta :=
    NatTransPrefixComponentCarrier_vert_comp_hsame_transport
      (hsame_refl p) (hsame_refl r) (hsame_refl a) sameTail left right etathetaRel
  have readback :
      NatTransPrefixComponentCarrier p r a displayed -> hsame etatheta displayed :=
    (NatTransPrefixComponentCarrier_vert_comp_public_readback left right etathetaRel).right
  exact And.intro forwardCarrier
    (And.intro reverseCarrier
      (And.intro sameTail
        (fun displayedCarrier =>
          And.intro (readback displayedCarrier)
            (hsame_trans (hsame_symm sameTail) (readback displayedCarrier)))))

end BEDC.Derived.NatTransUp
