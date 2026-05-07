import BEDC.Derived.CommRingUp
import BEDC.Derived.IdealUp

namespace BEDC.Derived.DedekindUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.CommRingUp

theorem DedekindSingleton_source_obligation :
    (exists h : BHist, CommRingSingletonCarrier h ∧
      CommRingSingletonClassifier h BHist.Empty) ∧
      (forall {h k : BHist}, CommRingSingletonClassifier h k ->
        CommRingSingletonCarrier h ∧ CommRingSingletonCarrier k ∧ hsame h k) ∧
      (forall {h : BHist}, CommRingSingletonCarrier h ->
        CommRingSingletonClassifier h BHist.Empty) ∧
      (forall {h k r : BHist}, CommRingSingletonClassifier h k ->
        CommRingSingletonClassifier k r -> CommRingSingletonClassifier h r) := by
  have emptyCarrier : CommRingSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassified : CommRingSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  constructor
  · exact Exists.intro BHist.Empty (And.intro emptyCarrier emptyClassified)
  · constructor
    · intro h k classified
      exact classified
    · constructor
      · intro h carrier
        exact And.intro carrier (And.intro emptyCarrier carrier)
      · intro h k r classifiedHK classifiedKR
        exact And.intro classifiedHK.left
          (And.intro classifiedKR.right.left
            (hsame_trans classifiedHK.right.right classifiedKR.right.right))

theorem DedekindSingleton_classifier_ledger_obligation :
    SemanticNameCert CommRingSingletonCarrier CommRingSingletonCarrier
      CommRingSingletonCarrier CommRingSingletonClassifier ∧
      (exists h : BHist, CommRingSingletonCarrier h) ∧
      (forall {h k : BHist}, CommRingSingletonClassifier h k -> hsame h k) ∧
      (forall {h : BHist}, CommRingSingletonCarrier h -> hsame h BHist.Empty) := by
  have commRingCert :
      SemanticNameCert CommRingSingletonCarrier CommRingSingletonCarrier
        CommRingSingletonCarrier CommRingSingletonClassifier :=
    singleton_empty_history_commring_laws.left
  have emptyCarrier : CommRingSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  constructor
  · exact commRingCert
  · constructor
    · exact Exists.intro BHist.Empty emptyCarrier
    · constructor
      · intro h k classified
        exact classified.right.right
      · intro h carrier
        exact carrier

end BEDC.Derived.DedekindUp
