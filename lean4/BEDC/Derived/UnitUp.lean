import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.UnitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

def UnitHistoryCarrier (h : BHist) : Prop :=
  Cont BHist.Empty h BHist.Empty

def UnitHistoryClassifier (h k : BHist) : Prop :=
  UnitHistoryCarrier h ∧ UnitHistoryCarrier k ∧ hsame h k

theorem UnitHistoryClassifier_semanticNameCert :
    SemanticNameCert UnitHistoryCarrier UnitHistoryCarrier UnitHistoryCarrier
      UnitHistoryClassifier := by
  constructor
  · constructor
    · exact Exists.intro BHist.Empty (cont_left_unit BHist.Empty)
    · intro h carrier
      exact And.intro carrier (And.intro carrier (hsame_refl h))
    · intro h k same
      exact And.intro same.right.left
        (And.intro same.left (hsame_symm same.right.right))
    · intro h k r sameHK sameKR
      exact And.intro sameHK.left
        (And.intro sameKR.right.left (hsame_trans sameHK.right.right sameKR.right.right))
    · intro h k same _carrier
      exact same.right.left
  · intro h source
    exact source
  · intro h source
    exact source

end BEDC.Derived.UnitUp
