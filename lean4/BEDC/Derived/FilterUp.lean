import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.FilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem FilterPrincipalEmptyCarrier_semanticNameCert :
    SemanticNameCert (fun h : BHist => UnaryHistory h ∧ hsame h BHist.Empty)
      (fun h : BHist => UnaryHistory h ∧ hsame h BHist.Empty)
      (fun h : BHist => UnaryHistory h ∧ hsame h BHist.Empty) hsame := by
  constructor
  · constructor
    · exact Exists.intro BHist.Empty (And.intro unary_empty (hsame_refl BHist.Empty))
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrier
      exact And.intro (unary_transport carrier.left same)
        (hsame_trans (hsame_symm same) carrier.right)
  · intro h source
    exact source
  · intro h source
    exact source

end BEDC.Derived.FilterUp
