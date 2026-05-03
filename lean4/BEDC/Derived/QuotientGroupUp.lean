import BEDC.Derived.SubgroupUp

namespace BEDC.Derived.QuotientGroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.SubgroupUp

def CentralizerCosetCarrier (mul : BHist -> BHist -> BHist) (a repr h : BHist) : Prop :=
  SubgroupCentralizerCarrier mul a repr ∧ hsame h repr

def CentralizerCosetClassifier (mul : BHist -> BHist -> BHist) (a repr h k : BHist) : Prop :=
  CentralizerCosetCarrier mul a repr h ∧ CentralizerCosetCarrier mul a repr k ∧ hsame h k

theorem CentralizerCoset_semanticNameCert {mul : BHist -> BHist -> BHist} {a repr : BHist}
    (reprCentral : SubgroupCentralizerCarrier mul a repr) :
    SemanticNameCert (CentralizerCosetCarrier mul a repr)
      (CentralizerCosetCarrier mul a repr) (CentralizerCosetCarrier mul a repr)
      (CentralizerCosetClassifier mul a repr) := by
  constructor
  · constructor
    · exact Exists.intro repr (And.intro reprCentral (hsame_refl repr))
    · intro h carrier
      exact And.intro carrier (And.intro carrier (hsame_refl h))
    · intro h k classified
      exact And.intro classified.right.left
        (And.intro classified.left (hsame_symm classified.right.right))
    · intro h k r classifiedHK classifiedKR
      exact And.intro classifiedHK.left
        (And.intro classifiedKR.right.left
          (hsame_trans classifiedHK.right.right classifiedKR.right.right))
    · intro h k classified _carrierH
      exact classified.right.left
  · intro h carrier
    exact carrier
  · intro h carrier
    exact carrier

end BEDC.Derived.QuotientGroupUp
