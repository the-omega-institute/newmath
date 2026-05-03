import BEDC.FKernel.NameCert

namespace BEDC.Derived.EqtypeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def EqtypeClassCarrier (anchor : BHist) (h : BHist) : Prop :=
  hsame h anchor

theorem EqtypeClass_semanticNameCert {anchor : BHist} :
    SemanticNameCert (EqtypeClassCarrier anchor) (EqtypeClassCarrier anchor)
      (EqtypeClassCarrier anchor) hsame := by
  constructor
  · constructor
    · exact Exists.intro anchor (hsame_refl anchor)
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrier
      exact hsame_trans (hsame_symm same) carrier
  · intro h source
    exact source
  · intro h source
    exact source

end BEDC.Derived.EqtypeUp
