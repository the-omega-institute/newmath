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

end BEDC.Derived.NatTransUp
