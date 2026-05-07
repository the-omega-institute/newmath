import BEDC.Derived.CommRingUp
import BEDC.Derived.IdealUp

namespace BEDC.Derived.DedekindUp

open BEDC.Derived.CommRingUp
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem DedekindSingleton_shared_source_obligation :
    SemanticNameCert CommRingSingletonCarrier CommRingSingletonCarrier
      CommRingSingletonCarrier CommRingSingletonClassifier ∧
      ((forall {x : BHist},
        CommRingSingletonCarrier x ∧ CommRingSingletonClassifier x BHist.Empty ->
          CommRingSingletonCarrier x) ∧
        (CommRingSingletonCarrier BHist.Empty ∧
          CommRingSingletonClassifier BHist.Empty BHist.Empty) ∧
        (forall {x y : BHist},
          CommRingSingletonCarrier x ∧ CommRingSingletonClassifier x BHist.Empty ->
            CommRingSingletonCarrier y ∧ CommRingSingletonClassifier y BHist.Empty ->
              CommRingSingletonCarrier (CommRingSingletonAdd x y) ∧
                CommRingSingletonClassifier (CommRingSingletonAdd x y) BHist.Empty) ∧
        (forall {x : BHist},
          CommRingSingletonCarrier x ∧ CommRingSingletonClassifier x BHist.Empty ->
            CommRingSingletonCarrier (CommRingSingletonNeg x) ∧
              CommRingSingletonClassifier (CommRingSingletonNeg x) BHist.Empty) ∧
        (forall {x y : BHist},
          CommRingSingletonCarrier x ∧ CommRingSingletonClassifier x BHist.Empty ->
            CommRingSingletonCarrier y ∧ CommRingSingletonClassifier y BHist.Empty ->
              CommRingSingletonCarrier (CommRingSingletonMul x y) ∧
                CommRingSingletonClassifier (CommRingSingletonMul x y) BHist.Empty)) := by
  have emptyCarrier : CommRingSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassified : CommRingSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro BHist.Empty emptyCarrier
        equiv_refl := by
          intro h carrier
          exact And.intro carrier (And.intro carrier (hsame_refl h))
        equiv_symm := by
          intro h k same
          exact And.intro same.right.left
            (And.intro same.left (hsame_symm same.right.right))
        equiv_trans := by
          intro h k r sameHK sameKR
          exact And.intro sameHK.left
            (And.intro sameKR.right.left
              (hsame_trans sameHK.right.right sameKR.right.right))
        carrier_respects_equiv := by
          intro h k same _carrier
          exact same.right.left
      }
      pattern_sound := by
        intro h carrier
        exact carrier
      ledger_sound := by
        intro h carrier
        exact carrier
    }
  · constructor
    · intro x sourceRow
      exact sourceRow.left
    · constructor
      · exact And.intro emptyCarrier emptyClassified
      · constructor
        · intro x y _sourceX _sourceY
          exact And.intro emptyCarrier emptyClassified
        · constructor
          · intro x _sourceX
            exact And.intro emptyCarrier emptyClassified
          · intro x y _sourceX _sourceY
            exact And.intro emptyCarrier emptyClassified

theorem DedekindSingleton_domain_law_obligation :
    (forall {x : BHist}, CommRingSingletonCarrier x ->
      CommRingSingletonClassifier x BHist.Empty) ∧
      (forall {x y : BHist}, CommRingSingletonCarrier x -> CommRingSingletonCarrier y ->
        CommRingSingletonClassifier (CommRingSingletonAdd x y) BHist.Empty ∧
          CommRingSingletonClassifier (CommRingSingletonNeg x) BHist.Empty ∧
          CommRingSingletonClassifier (CommRingSingletonMul x y) BHist.Empty) ∧
      (forall {p i : BHist}, CommRingSingletonCarrier p -> CommRingSingletonCarrier i ->
        CommRingSingletonClassifier (CommRingSingletonMul p i) BHist.Empty ∧
          CommRingSingletonClassifier (CommRingSingletonMul i p) BHist.Empty) := by
  have emptyCarrier : CommRingSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassified : CommRingSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  constructor
  · intro x carrierX
    exact And.intro carrierX (And.intro emptyCarrier carrierX)
  · constructor
    · intro x y _carrierX _carrierY
      exact And.intro emptyClassified (And.intro emptyClassified emptyClassified)
    · intro p i _carrierP _carrierI
      exact And.intro emptyClassified emptyClassified

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

theorem DedekindSingleton_scoped_certificate_packet :
    (SemanticNameCert CommRingSingletonCarrier CommRingSingletonCarrier CommRingSingletonCarrier
      CommRingSingletonClassifier) ∧
      (∃ h : BHist, CommRingSingletonCarrier h ∧
        CommRingSingletonClassifier h BHist.Empty) ∧
      (∀ {h k : BHist}, CommRingSingletonClassifier h k ->
        hsame h BHist.Empty ∧ hsame k BHist.Empty ∧ hsame h k) ∧
      (∀ {h : BHist}, CommRingSingletonCarrier h ->
        hsame (CommRingSingletonMul h BHist.Empty) BHist.Empty ∧
          hsame (CommRingSingletonMul BHist.Empty h) BHist.Empty) ∧
      (∀ {h k : BHist}, CommRingSingletonClassifier h k ->
        CommRingSingletonClassifier (CommRingSingletonAdd h k) BHist.Empty) := by
  have singletonLaws := singleton_empty_history_commring_laws
  have sourceRows := DedekindSingleton_source_obligation
  constructor
  · exact singletonLaws.left
  · constructor
    · exact sourceRows.left
    · constructor
      · intro h k classified
        exact And.intro classified.left
          (And.intro classified.right.left classified.right.right)
      · constructor
        · intro h _carrier
          exact And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)
        · intro h k classified
          exact singletonLaws.right.left classified.left classified.right.left

end BEDC.Derived.DedekindUp
