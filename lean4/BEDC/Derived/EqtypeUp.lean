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

theorem EqtypeIdentity_semanticNameCert :
    SemanticNameCert (fun h : BHist => hsame h h)
      (fun h : BHist => hsame h h)
      (fun h : BHist => hsame h h)
      hsame := by
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty (hsame_refl BHist.Empty)
      equiv_refl := by
        intro h _carrier
        exact hsame_refl h
      equiv_symm := by
        intro _h _k same
        exact hsame_symm same
      equiv_trans := by
        intro _h _k _r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro _h k _same _carrier
        exact hsame_refl k
    }
    pattern_sound := by
      intro _h carrier
      exact carrier
    ledger_sound := by
      intro _h carrier
      exact carrier
  }

end BEDC.Derived.EqtypeUp
