import BEDC.Derived.NatTransUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.NatTransUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.Derived.CategoryUp

theorem NatTransPrefixComponentCarrier_empty_component_semanticNameCert {p q a : BHist}
    (emptyComponent : NatTransPrefixComponentCarrier p q a BHist.Empty) :
    SemanticNameCert (NatTransPrefixComponentCarrier p q a)
      (NatTransPrefixComponentCarrier p q a) (NatTransPrefixComponentCarrier p q a)
        hsame := by
  constructor
  · constructor
    · exact Exists.intro BHist.Empty emptyComponent
    · intro h _componentCarrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same componentCarrier
      exact
        And.intro componentCarrier.left
          (And.intro componentCarrier.right.left
            (And.intro componentCarrier.right.right.left
              (CategoryHomCarrier_hsame_transport
                (hsame_refl (append p a)) (hsame_refl (append q a)) same
                  componentCarrier.right.right.right)))
  · intro h source
    exact source
  · intro h source
    exact source

end BEDC.Derived.NatTransUp
